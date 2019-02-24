------------------------------------------------------------------------------
-- DynASM ARM module.
--
-- Copyright (C) 2005-2017 Mike Pall. All rights reserved.
-- See dynasm.lua for full copyright notice.
------------------------------------------------------------------------------

-- Module information:
local _info = {
  arch =        "armv7a",
  description =        "DynASM ARMv7A module",
  version =        "1.5.0",
  vernum =         10500,
  release =        "2019-02-23",
  author =        "Mike Pall, Andy Martin",
  license =        "MIT",
}

-- Exported glue functions for the arch-specific module.
local _M = { _info = _info }

-- Cache library functions.
local type, tonumber, pairs, ipairs = type, tonumber, pairs, ipairs
local assert, setmetatable, rawget = assert, setmetatable, rawget
local _s = string
local sub, format, byte, char = _s.sub, _s.format, _s.byte, _s.char
local match, gmatch, gsub = _s.match, _s.gmatch, _s.gsub
local concat, sort, insert = table.concat, table.sort, table.insert
local bit = bit or require("bit")
local band, bor, shl, shr, sar = bit.band, bit.bor, bit.lshift, bit.rshift, bit.arshift
local ror, tohex = bit.ror, bit.tohex

-- Inherited tables and callbacks.
local g_opt, g_arch
local wline, werror, wfatal, wwarn

-- Action name list.
-- CHECK: Keep this in sync with the C code!
local action_names = {
  -- 0 args
  "STOP", "SECTION", "ESC", "REL_EXT",
  -- n args (self-handled)
  "SRLIST",
  -- 0 args + buffer pos
  "ALIGN", "REL_LG", "LABEL_LG",
  -- 1 arg
  "REL_PC", "REL_APC", "LABEL_PC",
  "IMM", "IMM12", "IMM16", "IMM32",
  "IMML8", "IMML12", "IMMV8", "IMMSHIFT",
  -- 2 args
  "VRLIST",
}

-- Maximum number of section buffer positions for dasm_put().
-- CHECK: Keep this in sync with the C code!
local maxsecpos = 25 -- Keep this low, to avoid excessively long C lines.

-- Action name -> action number.
local map_action = {}
for n,name in ipairs(action_names) do
  map_action[name] = n-1
end

-- Action list buffer.
local actlist = {}

-- Argument list for next dasm_put(). Start with offset 0 into action list.
local actargs = { 0 }

-- Current number of section buffer positions for dasm_put().
local secpos = 1

------------------------------------------------------------------------------

-- Dump action names and numbers.
local function dumpactions(out)
  out:write("DynASM encoding engine action codes:\n")
  for n,name in ipairs(action_names) do
    local num = map_action[name]
    out:write(format("  %-10s %02X  %d\n", name, num, num))
  end
  out:write("\n")
end

-- Write action list buffer as a huge static C array.
local function writeactions(out, name)
  local nn = #actlist
  if nn == 0 then nn = 1; actlist[0] = map_action.STOP end
  out:write("static const unsigned int ", name, "[", nn, "] = {\n")
  for i = 1,nn-1 do
    assert(out:write("0x", tohex(actlist[i]), ",\n"))
  end
  assert(out:write("0x", tohex(actlist[nn]), "\n};\n\n"))
end

------------------------------------------------------------------------------

-- Add word to action list.
local function wputxw(n)
  assert(n >= 0 and n <= 0xffffffff and n % 1 == 0, "word out of range")
  actlist[#actlist+1] = n
end

-- Add action to list with optional arg. Advance buffer pos, too.
local function waction(action, val, a, num)
  local w = assert(map_action[action], "bad action name `"..action.."'")
  wputxw(w * 0x10000 + (val or 0))
  if a then actargs[#actargs+1] = a end
  if a or num then secpos = secpos + (num or 1) end
end

-- Add action to list with two args. Advance buffer pos, too.
local function waction2(action, val, a, a2)
  local w = assert(map_action[action], "bad action name `"..action.."'")
  wputxw(w * 0x10000 + (val or 0))
  if not a or not a2 then
    werror("waction2: both args are mandatory, if you don't need them use waction")
  end
  actargs[#actargs+1] = a
  actargs[#actargs+1] = a2
  secpos = secpos + 2
end

-- Add action to list with N args. Advance buffer pos, too.
local function wactionn(action, val, al)
  local w = assert(map_action[action], "bad action name `"..action.."'")
  wputxw(w * 0x10000 + (val or 0))
  for i,a in ipairs(al) do
    actargs[#actargs+1] = a
  end
  secpos = secpos + #al
end

local function wimmaction(arg, scale, bits, shift, isoffset)
  return waction("IMM", (isoffset and 32768 or 0)+scale*1024+bits*32+shift, arg)
end

-- Flush action list (intervening C code or buffer pos overflow).
local function wflush(term)
  if #actlist == actargs[1] then return end -- Nothing to flush.
  if not term then waction("STOP") end -- Terminate action list.
  wline(format("dasm_put(Dst, %s);", concat(actargs, ", ")), true)
  actargs = { #actlist } -- Actionlist offset is 1st arg to next dasm_put().
  secpos = 1 -- The actionlist offset occupies a buffer position, too.
end

-- Put escaped word.
local function wputw(n)
  if n <= 0x001fffff then waction("ESC") end
  wputxw(n)
end

-- Reserve position for word.
local function wpos()
  local pos = #actlist+1
  actlist[pos] = ""
  return pos
end

-- Store word to reserved position.
local function wputpos(pos, n)
  assert(n >= 0 and n <= 0xffffffff and n % 1 == 0, "word out of range")
  if n <= 0x001fffff then
    insert(actlist, pos+1, n)
    n = map_action.ESC * 0x10000
  end
  actlist[pos] = n
end

------------------------------------------------------------------------------

-- Global label name -> global label number. With auto assignment on 1st use.
local next_global = 20
local map_global = setmetatable({}, { __index = function(t, name)
  if not match(name, "^[%a_][%w_]*$") then werror("bad global label") end
  local n = next_global
  if n > 2047 then werror("too many global labels") end
  next_global = n + 1
  t[name] = n
  return n
end})

-- Dump global labels.
local function dumpglobals(out, lvl)
  local t = {}
  for name, n in pairs(map_global) do t[n] = name end
  out:write("Global labels:\n")
  for i=20,next_global-1 do
    out:write(format("  %s\n", t[i]))
  end
  out:write("\n")
end

-- Write global label enum.
local function writeglobals(out, prefix)
  local t = {}
  for name, n in pairs(map_global) do t[n] = name end
  out:write("enum {\n")
  for i=20,next_global-1 do
    out:write("  ", prefix, t[i], ",\n")
  end
  out:write("  ", prefix, "_MAX\n};\n")
end

-- Write global label names.
local function writeglobalnames(out, name)
  local t = {}
  for name, n in pairs(map_global) do t[n] = name end
  out:write("static const char *const ", name, "[] = {\n")
  for i=20,next_global-1 do
    out:write("  \"", t[i], "\",\n")
  end
  out:write("  (const char *)0\n};\n")
end

------------------------------------------------------------------------------

-- Extern label name -> extern label number. With auto assignment on 1st use.
local next_extern = 0
local map_extern_ = {}
local map_extern = setmetatable({}, { __index = function(t, name)
  -- No restrictions on the name for now.
  local n = next_extern
  if n > 2047 then werror("too many extern labels") end
  next_extern = n + 1
  t[name] = n
  map_extern_[n] = name
  return n
end})

-- Dump extern labels.
local function dumpexterns(out, lvl)
  out:write("Extern labels:\n")
  for i=0,next_extern-1 do
    out:write(format("  %s\n", map_extern_[i]))
  end
  out:write("\n")
end

-- Write extern label names.
local function writeexternnames(out, name)
  out:write("static const char *const ", name, "[] = {\n")
  for i=0,next_extern-1 do
    out:write("  \"", map_extern_[i], "\",\n")
  end
  out:write("  (const char *)0\n};\n")
end

------------------------------------------------------------------------------

-- Arch-specific maps.

-- Ext. register name -> int. name.
local map_archdef = { sp = "r13", lr = "r14", pc = "r15", }

-- Int. register name -> ext. name.
local map_reg_rev = { r13 = "sp", r14 = "lr", r15 = "pc", }

local map_type = {}                -- Type name -> { ctype, reg }
local ctypenum = 0                -- Type number (for Dt... macros).

-- Reverse defines for registers.
function _M.revdef(s)
  return map_reg_rev[s] or s
end

local map_shift = { lsl = 0, lsr = 1, asr = 2, ror = 3, }

local map_cond = {
  eq = 0, ne = 1, cs = 2, cc = 3, mi = 4, pl = 5, vs = 6, vc = 7,
  hi = 8, ls = 9, ge = 10, lt = 11, gt = 12, le = 13, al = 14,
  hs = 2, lo = 3,
}

------------------------------------------------------------------------------

-- Template strings for ARM instructions.
local map_op = {
  -- Basic data processing instructions.
  and_3 = "e0000000DNPs",
  eor_3 = "e0200000DNPs",
  sub_3 = "e0400000DNPs",
  rsb_3 = "e0600000DNPs",
  add_3 = "e0800000DNPs",
  adc_3 = "e0a00000DNPs",
  sbc_3 = "e0c00000DNPs",
  rsc_3 = "e0e00000DNPs",
  tst_2 = "e1100000NP",
  teq_2 = "e1300000NP",
  cmp_2 = "e1500000NP",
  cmn_2 = "e1700000NP",
  orr_3 = "e1800000DNPs",
  mov_2 = "e1a00000DPs",
  bic_3 = "e1c00000DNPs",
  mvn_2 = "e1e00000DPs",

  and_4 = "e0000000DNMps",
  eor_4 = "e0200000DNMps",
  sub_4 = "e0400000DNMps",
  rsb_4 = "e0600000DNMps",
  add_4 = "e0800000DNMps",
  adc_4 = "e0a00000DNMps",
  sbc_4 = "e0c00000DNMps",
  rsc_4 = "e0e00000DNMps",
  tst_3 = "e1100000NMp",
  teq_3 = "e1300000NMp",
  cmp_3 = "e1500000NMp",
  cmn_3 = "e1700000NMp",
  orr_4 = "e1800000DNMps",
  mov_3 = "e1a00000DMps",
  bic_4 = "e1c00000DNMps",
  mvn_3 = "e1e00000DMps",

  lsl_3 = "e1a00000DMws",
  lsr_3 = "e1a00020DMws",
  asr_3 = "e1a00040DMws",
  ror_3 = "e1a00060DMws",
  rrx_2 = "e1a00060DMs",

  -- Multiply and multiply-accumulate.
  mul_3 = "e0000090NMSs",
  mla_4 = "e0200090NMSDs",
  umaal_4 = "e0400090DNMSs",        -- v6
  mls_4 = "e0600090DNMSs",        -- v6T2
  umull_4 = "e0800090DNMSs",
  umlal_4 = "e0a00090DNMSs",
  smull_4 = "e0c00090DNMSs",
  smlal_4 = "e0e00090DNMSs",

  -- Halfword multiply and multiply-accumulate.
  smlabb_4 = "e1000080NMSD",        -- v5TE
  smlatb_4 = "e10000a0NMSD",        -- v5TE
  smlabt_4 = "e10000c0NMSD",        -- v5TE
  smlatt_4 = "e10000e0NMSD",        -- v5TE
  smlawb_4 = "e1200080NMSD",        -- v5TE
  smulwb_3 = "e12000a0NMS",        -- v5TE
  smlawt_4 = "e12000c0NMSD",        -- v5TE
  smulwt_3 = "e12000e0NMS",        -- v5TE
  smlalbb_4 = "e1400080NMSD",        -- v5TE
  smlaltb_4 = "e14000a0NMSD",        -- v5TE
  smlalbt_4 = "e14000c0NMSD",        -- v5TE
  smlaltt_4 = "e14000e0NMSD",        -- v5TE
  smulbb_3 = "e1600080NMS",        -- v5TE
  smultb_3 = "e16000a0NMS",        -- v5TE
  smulbt_3 = "e16000c0NMS",        -- v5TE
  smultt_3 = "e16000e0NMS",        -- v5TE

  -- Miscellaneous data processing instructions.
  clz_2 = "e16f0f10DM", -- v5T
  rev_2 = "e6bf0f30DM", -- v6
  rev16_2 = "e6bf0fb0DM", -- v6
  revsh_2 = "e6ff0fb0DM", -- v6
  sel_3 = "e6800fb0DNM", -- v6
  usad8_3 = "e780f010NMS", -- v6
  usada8_4 = "e7800010NMSD", -- v6
  rbit_2 = "e6ff0f30DM", -- v6T2
  movw_2 = "e3000000DW", -- v6T2
  movt_2 = "e3400000DW", -- v6T2
  sbfx_4 = "e7a00050DMvt", -- v6T2
  ubfx_4 = "e7e00050DMvt", -- v6T2
  -- Note: the X encodes the msb field, not the width.
  bfc_3 = "e7c0001fDvX", -- v6T2
  bfi_4 = "e7c00010DMvX", -- v6T2

  -- Packing and unpacking instructions.
  pkhbt_3 = "e6800010DNM", pkhbt_4 = "e6800010DNMv", -- v6
  pkhtb_3 = "e6800050DNM", pkhtb_4 = "e6800050DNMv", -- v6
  sxtab_3 = "e6a00070DNM", sxtab_4 = "e6a00070DNMv", -- v6
  sxtab16_3 = "e6800070DNM", sxtab16_4 = "e6800070DNMv", -- v6
  sxtah_3 = "e6b00070DNM", sxtah_4 = "e6b00070DNMv", -- v6
  sxtb_2 = "e6af0070DM", sxtb_3 = "e6af0070DMv", -- v6
  sxtb16_2 = "e68f0070DM", sxtb16_3 = "e68f0070DMv", -- v6
  sxth_2 = "e6bf0070DM", sxth_3 = "e6bf0070DMv", -- v6
  uxtab_3 = "e6e00070DNM", uxtab_4 = "e6e00070DNMv", -- v6
  uxtab16_3 = "e6c00070DNM", uxtab16_4 = "e6c00070DNMv", -- v6
  uxtah_3 = "e6f00070DNM", uxtah_4 = "e6f00070DNMv", -- v6
  uxtb_2 = "e6ef0070DM", uxtb_3 = "e6ef0070DMv", -- v6
  uxtb16_2 = "e6cf0070DM", uxtb16_3 = "e6cf0070DMv", -- v6
  uxth_2 = "e6ff0070DM", uxth_3 = "e6ff0070DMv", -- v6

  -- Saturating instructions.
  qadd_3 = "e1000050DMN",        -- v5TE
  qsub_3 = "e1200050DMN",        -- v5TE
  qdadd_3 = "e1400050DMN",        -- v5TE
  qdsub_3 = "e1600050DMN",        -- v5TE
  ssat_3 = "e6a00010DtM", ssat_4 = "e6a00010DtMp", -- v6
  usat_3 = "e6e00010DXM", usat_4 = "e6e00010DXMp", -- v6
  ssat16_3 = "e6a00f30DXM", -- v6
  usat16_3 = "e6e00f30DXM", -- v6

  -- Parallel addition and subtraction.
  sadd16_3 = "e6100f10DNM", -- v6
  sasx_3 = "e6100f30DNM", -- v6
  ssax_3 = "e6100f50DNM", -- v6
  ssub16_3 = "e6100f70DNM", -- v6
  sadd8_3 = "e6100f90DNM", -- v6
  ssub8_3 = "e6100ff0DNM", -- v6
  qadd16_3 = "e6200f10DNM", -- v6
  qasx_3 = "e6200f30DNM", -- v6
  qsax_3 = "e6200f50DNM", -- v6
  qsub16_3 = "e6200f70DNM", -- v6
  qadd8_3 = "e6200f90DNM", -- v6
  qsub8_3 = "e6200ff0DNM", -- v6
  shadd16_3 = "e6300f10DNM", -- v6
  shasx_3 = "e6300f30DNM", -- v6
  shsax_3 = "e6300f50DNM", -- v6
  shsub16_3 = "e6300f70DNM", -- v6
  shadd8_3 = "e6300f90DNM", -- v6
  shsub8_3 = "e6300ff0DNM", -- v6
  uadd16_3 = "e6500f10DNM", -- v6
  uasx_3 = "e6500f30DNM", -- v6
  usax_3 = "e6500f50DNM", -- v6
  usub16_3 = "e6500f70DNM", -- v6
  uadd8_3 = "e6500f90DNM", -- v6
  usub8_3 = "e6500ff0DNM", -- v6
  uqadd16_3 = "e6600f10DNM", -- v6
  uqasx_3 = "e6600f30DNM", -- v6
  uqsax_3 = "e6600f50DNM", -- v6
  uqsub16_3 = "e6600f70DNM", -- v6
  uqadd8_3 = "e6600f90DNM", -- v6
  uqsub8_3 = "e6600ff0DNM", -- v6
  uhadd16_3 = "e6700f10DNM", -- v6
  uhasx_3 = "e6700f30DNM", -- v6
  uhsax_3 = "e6700f50DNM", -- v6
  uhsub16_3 = "e6700f70DNM", -- v6
  uhadd8_3 = "e6700f90DNM", -- v6
  uhsub8_3 = "e6700ff0DNM", -- v6

  -- Load/store instructions.
  str_2 = "e4000000DL", str_3 = "e4000000DL", str_4 = "e4000000DL",
  strb_2 = "e4400000DL", strb_3 = "e4400000DL", strb_4 = "e4400000DL",
  ldr_2 = "e4100000DL", ldr_3 = "e4100000DL", ldr_4 = "e4100000DL",
  ldrb_2 = "e4500000DL", ldrb_3 = "e4500000DL", ldrb_4 = "e4500000DL",
  strh_2 = "e00000b0DL", strh_3 = "e00000b0DL",
  ldrh_2 = "e01000b0DL", ldrh_3 = "e01000b0DL",
  ldrd_2 = "e00000d0SDL", ldrd_3 = "e00000d0SDL", -- v5TE
  ldrsb_2 = "e01000d0DL", ldrsb_3 = "e01000d0DL",
  strd_2 = "e00000f0SDL", strd_3 = "e00000f0SDL", -- v5TE
  ldrsh_2 = "e01000f0DL", ldrsh_3 = "e01000f0DL",

  ldm_2 = "e8900000oR", ldmia_2 = "e8900000oR", ldmfd_2 = "e8900000oR",
  ldmda_2 = "e8100000oR", ldmfa_2 = "e8100000oR",
  ldmdb_2 = "e9100000oR", ldmea_2 = "e9100000oR",
  ldmib_2 = "e9900000oR", ldmed_2 = "e9900000oR",
  stm_2 = "e8800000oR", stmia_2 = "e8800000oR", stmfd_2 = "e8800000oR",
  stmda_2 = "e8000000oR", stmfa_2 = "e8000000oR",
  stmdb_2 = "e9000000oR", stmea_2 = "e9000000oR",
  stmib_2 = "e9800000oR", stmed_2 = "e9800000oR",
  pop_1 = "e8bd0000R", push_1 = "e92d0000R",

  -- Branch instructions.
  b_1 = "ea000000B",
  bl_1 = "eb000000B",
  blx_1 = "e12fff30C",
  bx_1 = "e12fff10M",

  -- Miscellaneous instructions.
  nop_0 = "e1a00000",
  mrs_1 = "e10f0000D",
  bkpt_1 = "e1200070K", -- v5T
  svc_1 = "ef000000T", swi_1 = "ef000000T",
  ud_0 = "e7f001f0",

  -- VFP
  ["vadd.f64_3"] = "ee300b00Gdnm",
  ["vsub.f64_3"] = "ee300b40Gdnm",
  ["vmul.f64_3"] = "ee200b00Gdnm",
  ["vnmul.f32_3"] = "ee200a40dnm",
  ["vnmul.f64_3"] = "ee200b40Gdnm",
  ["vmla.f64_3"] = "ee000b00Gdnm",
  ["vmls.f64_3"] = "ee000b40Gdnm",
  ["vnmla.f32_3"] = "ee100a40dnm",
  ["vnmla.f64_3"] = "ee100b40Gdnm",
  ["vnmls.f32_3"] = "ee100a00dnm",
  ["vnmls.f64_3"] = "ee100b00Gdnm",
  ["vdiv.f32_3"] = "ee800a00dnm",
  ["vdiv.f64_3"] = "ee800b00Gdnm",

  ["vabs.f64_2"] = "eeb00bc0Gdm",
  ["vneg.f64_2"] = "eeb10b40Gdm",
  ["vsqrt.f32_2"] = "eeb10ac0dm",
  ["vsqrt.f64_2"] = "eeb10bc0Gdm",
  ["vcmp.f32_2"] = "eeb40a40dm",
  ["vcmp.f64_2"] = "eeb40b40Gdm",
  ["vcmpe.f32_2"] = "eeb40ac0dm",
  ["vcmpe.f64_2"] = "eeb40bc0Gdm",
  ["vcmpz.f32_1"] = "eeb50a40d",
  ["vcmpz.f64_1"] = "eeb50b40Gd",
  ["vcmpze.f32_1"] = "eeb50ac0d",
  ["vcmpze.f64_1"] = "eeb50bc0Gd",

  vldr_2 = "ed100a00dl|ed100b00Gdl",
  vstr_2 = "ed000a00dl|ed000b00Gdl",
  vldm_2 = "ec900a00or",
  vldmia_2 = "ec900a00or",
  vldmdb_2 = "ed100a00or",
  vpop_1 = "ecbd0a00r",
  vstm_2 = "ec800a00or",
  vstmia_2 = "ec800a00or",
  vstmdb_2 = "ed000a00or",
  vpush_1 = "ed2d0a00r",

  ["vmov.f32_2"] = "eeb00a40dm|eeb00a00dY",        -- #imm is VFPv3 only
  ["vmov.f64_2"] = "eeb00b40Gdm|eeb00b00GdY",        -- #imm is VFPv3 only
  vmov_3 = "ec500a10DNm|ec400a10mDN|ec500b10GDNm|ec400b10GmDN",

  vmrs_0 = "eef1fa10",
  vmrs_1 = "eef10a10D",
  vmsr_1 = "eee10a10D",

  ["vcvt.s32.f64_2"] = "eebd0bc0dGm",
  ["vcvt.u32.f64_2"] = "eebc0bc0dGm",
  ["vcvtr.s32.f32_2"] = "eebd0a40dm",
  ["vcvtr.s32.f64_2"] = "eebd0b40dGm",
  ["vcvtr.u32.f32_2"] = "eebc0a40dm",
  ["vcvtr.u32.f64_2"] = "eebc0b40dGm",
  ["vcvt.f64.s32_2"] = "eeb80bc0GdFm",
  ["vcvt.f64.u32_2"] = "eeb80b40GdFm",
  ["vcvt.f32.f64_2"] = "eeb70bc0dGm",
  ["vcvt.f64.f32_2"] = "eeb70ac0GdFm",

  -- VFPv4 only:
  ["vfma.f64_3"] = "eea00b00Gdnm",
  ["vfms.f64_3"] = "eea00b40Gdnm",
  ["vfnma.f32_3"] = "ee900a40dnm",
  ["vfnma.f64_3"] = "ee900b40Gdnm",
  ["vfnms.f32_3"] = "ee900a00dnm",
  ["vfnms.f64_3"] = "ee900b00Gdnm",

  -- NEON/VFP
  ["vhadd._3"] = "f2000040QdnmU|f2000000GdnmU",
  ["vhsub._3"] = "f2000240QdnmU|f2000200GdnmU",
  ["vqadd._3"] = "f2000050QdnmU|f2000010GdnmU",
  ["vqsub._3"] = "f2000250QdnmU|f2000210GdnmU",
  ["vrhadd._3"] = "f2000140QdnmU|f2000100GdnmU",
  vand_3 = "f2000150Qdnm|f2000110Gdnm",
  vbic_3 = "f2100150Qdnm|f2100110Gdnm",
  vorr_3 = "f2200150Qdnm|f2200110Gdnm",
  vmov_2 = "f2200150Qdz|f2200110Gdz|ee100a10Dn|ee000a10nD",
  vorn_3 = "f2300150Qdnm|f2300110Gdnm",
  veor_3 = "f3000150Qdnm|f3000110Gdnm",
  vbsl_3 = "f2100150Qdnm|f2100110Gdnm",
  vbit_3 = "f2200150Qdnm|f2200110Gdnm",
  vbif_3 = "f2300150Qdnm|f2300110Gdnm",
  ["vcgt._3"] = "f2000340QdnmU|f2000300GdnmU",
  ["vcge._3"] = "f2000350QdnmU|f2000310GdnmU",
  ["vshl._3"] = "f2000440QdnmU|f2000400GdnmU",
  ["vqshl._3"] = "f2000450QdnmU|f2000410GdnmU",
  ["vrshl._3"] = "f2000540QdnmU|f2000500GdnmU",
  ["vqrshl._3"] = "f2000550QdnmU|f2000510GdnmU",
  ["vmax._3"] = "f2000640QdnmU|f2000600GdnmU",
  ["vmin._3"] = "f2000650QdnmU|f2000610GdnmU",
  ["vabd._3"] = "f2000740QdnmU|f2000700GdnmU",
  ["vabdl._3"] = "f2800700QdGnmU",
  ["vaba._3"] = "f2000750QdnmU|f2000710GdnmU",
  ["vabal._3"] = "f2800500QdGnmU",
  ["vadd.i_3"] = "f2000840Qdnmu|f2000800Gdnmu",
  ["vadd.i64_3"] = "f2300840Qdnm|f2300800Gdnm",
  ["vsub.i_3"] = "f3000840Qdnmu|f3000800Gdnmu",
  ["vsub.i64_3"] = "f3300840Qdnm|f3300800Gdnm",
  ["vtst.i_3"] = "f2000850Qdnmu|f2000810Gdnmu",
  ["vceq.i_3"] = "f3000850Qdnmu|f3000810Gdnmu",
  ["vmla.i_3"] = "f2000940Qdnmu|f2000900Gdnmu",
  ["vmlal._3"] = "f2808800QdGnmU",
  ["vmls.i_3"] = "f3000940Qdnmu|f3000900Gdnmu",
  ["vmlsl._3"] = "f2808a00QdGnmU",
  ["vmul.i_3"] = "f2000950Qdnmu|f2000910Gdnmu",
  ["vmull._3"] = "f2808c00QdGnmU",
  ["vmul.p8_3"] = "f3000950Qdnm|f2000910Gdnm",
  ["vmull.p8_3"] = "f2808e00QdGnm",
  ["vmla.i16_3"] = "f3900040Qdnj|f2900040Gdnj|f3900440Qdnj|f2900440Gdnj",
  ["vmla.i32_3"] = "f3a00040Qdnj|f2a00040Gdnj|f3a00440Qdnj|f2a00440Gdnj",
  ["vmla.f32_3"] = "f3a00140Qdnj|f2a00140Gdnj|f2000d50Qdnm|f2000d10Gdnm|ee000a00dnm",
  ["vmlal.s16_3"] = "f2900240QdGnJ",
  ["vmlal.s32_3"] = "f2a00240QdGnJ",
  ["vmlal.u16_3"] = "f3900240QdGnJ",
  ["vmlal.u32_3"] = "f3a00240QdGnJ",
  ["vmls.i16_3"] = "f3900440Qdnj|f2900440Gdnj",
  ["vmls.i32_3"] = "f3a00440Qdnj|f2a00440Gdnj",
  ["vmls.f32_3"] = "f3a00540Qdnj|f2a00540Gdnj|f2200d50Qdnm|f2200d10Gdnm|ee000a40dnm",
  ["vmlsl.s16_3"] = "f2900640QdGnJ",
  ["vmlsl.s32_3"] = "f2a00640QdGnJ",
  ["vmlsl.u16_3"] = "f3900640QdGnJ",
  ["vmlsl.u32_3"] = "f3a00640QdGnJ",
  ["vmul.i16_3"] = "f3900840Qdnj|f2900840Gdnj",
  ["vmul.i32_3"] = "f3a00840Qdnj|f2a00840Gdnj",
  ["vmul.f32_3"] = "f3a00940Qdnj|f2a00940Gdnj|f3000d50Qdnm|f3000d10Gdnm|ee200a00dnm",
  ["vmull.s16_3"] = "f2900a40QdGnJ",
  ["vmull.s32_3"] = "f2a00a40QdGnJ",
  ["vmull.u16_3"] = "f3900a40QdGnJ",
  ["vmull.u32_3"] = "f3a00a40QdGnJ",
  ["vmls.f32_3"] = "f2200d50Qdnm|f2200d10Gdnm",
  ["vpmax._3"] = "f2000900GdnmU",
  ["vpmin._3"] = "f2000910GdnmU",
  ["vpadd.i_3"] = "f2000b10Gdnmu",
  ["vqdmulh.s16_3"] = "f2100b40Qdnm|f2100b00Gdnm|f3900c40Qdnk|f3900c40Qdnk",
  ["vqdmulh.s32_3"] = "f2200b40Qdnm|f2200b00Gdnm|f2a00c40Gdnl|f2a00c40Gdnl",
  ["vrqdmulh.s16_3"] = "f3100b40Qdnm|f3100b00Gdnm|f3900d40Qdnk|f2900d40Gdnk",
  ["vrqdmulh.s32_3"] = "f3200b40Qdnm|f3200b00Gdnm|f3a00d40Qdnl|f2a00d40Gdnl",
  ["vqdmull.s16_3"] = "f2900d00QdGnm|f2900b40QdGnk",
  ["vqdmull.s32_3"] = "f2a00d00QdGnm|f2a00b40QdGnl",
  ["vfma.f32_3"] = "f2000c50Qdnm|f2000c10Gdnm|eea00a00dnm", -- q/d ASIMDv2
  ["vfms.f32_3"] = "f2200c50Qdnm|f2200c10Gdnm|eea00a40dnm", -- q/d ASIMDv2
  ["vadd.f32_3"] = "f2000d40Qdnm|f2000d00Gdnm|ee300a00dnm",
  ["vsub.f32_3"] = "f2200d40Qdnm|f2200d00Gdnm|ee300a40dnm",
  ["vpadd.f32_3"] = "f3000d00Gdnm",
  ["vabd.f32_3"] = "f3200d40Qdnm|f3200d00Gdnm",
  ["vceq.f32_3"] = "f2000e40Qdnm|f2000e00Gdnm",
  ["vcge.f32_3"] = "f3000e40Qdnm|f3000e00Gdnm",
  ["vcgt.f32_3"] = "f3200e40Qdnm|f3200e00Gdnm",
  ["vcle.f32_3"] = "f3000e40Qdmn|f3000e00Gdmn",
  ["vclt.f32_3"] = "f3200e40Qdmn|f3200e00Gdmn",
  ["vacge.f32_3"] = "f3000e50Qdnm|f3000e10Gdnm",
  ["vacgt.f32_3"] = "f3200e50Qdnm|f3200e10Gdnm",
  ["vacle.f32_3"] = "f3000e50Qdmn|f3000e10Gdmn",
  ["vaclt.f32_3"] = "f3200e50Qdmn|f3200e10Gdmn",
  ["vmax.f32_3"] = "f2000f40Qdnm|f2000f00Gdnm",
  ["vmin.f32_3"] = "f2200f40Qdnm|f2200f00Gdnm",
  ["vpmax.f32_3"] = "f3000f40Qdnm|f3000f00Gdnm",
  ["vpmin.f32_3"] = "f3200f40Qdnm|f3200f00Gdnm",
  ["vrecps.f32_3"] = "f2000f50Qdnm|f2000f10Gdnm",
  ["vrsqrts.f32_3"] = "f2200f50Qdnm|f2200f10Gdnm",
  ["vaddl._3"] = "f2800000QdGnmU",
  ["vaddw._3"] = "f2800100QdnGmU",
  ["vsubl._3"] = "f2800200QdGnmU",
  ["vsubw._3"] = "f2800300QdnGmU",
  ["vaddhn.i16_3"] = "f2800400GdQnm",
  ["vaddhn.i32_3"] = "f2900400GdQnm",
  ["vaddhn.i64_3"] = "f2a00400GdQnm",
  ["vsubhn.i16_3"] = "f2800600GdQnm",
  ["vsubhn.i32_3"] = "f2900600GdQnm",
  ["vsubhn.i64_3"] = "f2a00600GdQnm",
  ["vqdmlal.s16_3"] = "f2900900QdGnm|f2900300QdGnk",
  ["vqdmlal.s32_3"] = "f2a00900QdGnm|f2a00300QdGnl",
  ["vqdmlsl.s16_3"] = "f2900b00QdGnm|f2900740QdGnk",
  ["vqdmlsl.s32_3"] = "f2a00b00QdGnm|f2a00740QdGnl",
  ["vshr.s_3"] = "f2800050Qdmy|f2800010Gdmy",
  ["vshr.u_3"] = "f3800050Qdmy|f3800010Gdmy",
  ["vsra.s_3"] = "f2800150Qdmy|f2800110Gdmy",
  ["vsra.u_3"] = "f3800150Qdmy|f3800110Gdmy",
  ["vrshr.s_3"] = "f2800250Qdmy|f2800210Gdmy",
  ["vrshr.u_3"] = "f3800250Qdmy|f3800210Gdmy",
  ["vrsra.s_3"] = "f2800350Qdmy|f2800310Gdmy",
  ["vrsra.u_3"] = "f3800350Qdmy|f3800310Gdmy",
  ["vsri._3"] = "f3800450Qdmy|f3800410Gdmy",
  ["vshl.i_3"] = "f2800550Qdmx|f2800510Gdmx",
  ["vsli._3"] = "f3800550Qdmx|f3800510Gdmx",
  ["vqshl.s_3"] = "f2800750Qdmx|f2800710Gdmx",
  ["vqshl.u_3"] = "f3800750Qdmx|f3800710Gdmx",
  ["vqshlu.s_3"] = "f3800650Qdmx|f3800610Gdmx",
  ["vshrn.i_3"] = "f2800810GdQmy",
  ["vrshrn.i_3"] = "f2800850GdQm?",   -- y but different
  ["vqshrn.s_3"] = "f2800910GdQm?",   -- y but different
  ["vqshrn.u_3"] = "f3800810GdQm?",   -- y but different
  ["vqshrun.s_3"] = "f3800910GdQm?",  -- y but different
  ["vqrshrn.s_3"] = "f2800950GdQm?",  -- y but different
  ["vqrshrn.u_3"] = "f3800950GdQm?",  -- y but different
  ["vqrshrun.s_3"] = "f3800850GdQm?", -- y but different
  ["vshll.s_3"] = "f2800a10QdGmx",    -- imm < size
  ["vshll.u_3"] = "f3800a10QdGmx",    -- imm < size
  ["vshll.i_3"] = "f3b20300QdGm???",  -- imm == size
  ["vmovl.s8_2"] = "f2880a10QdGm",
  ["vmovl.s16_2"] = "f2900a10QdGm",
  ["vmovl.s32_2"] = "f2a00a10QdGm",
  ["vmovl.u8_2"] = "f3880a10QdGm",
  ["vmovl.u16_2"] = "f3900a10QdGm",
  ["vmovl.u32_2"] = "f3a00a10QdGm",
  ["vcvt.s32.f32_3"] = "f2800f50Qdm?|f2800f10Gdm?",-- (64-imm6) at 16-- (64-imm6) at 16
  ["vcvt.u32.f32_3"] = "f3800f50Qdm?|f3800f10Gdm?",-- (64-imm6) at 16-- (64-imm6) at 16
  ["vcvt.f32.s32_3"] = "f2800e50Qdm?|f2800e10Gdm?",-- (64-imm6) at 16-- (64-imm6) at 16
  ["vcvt.f32.u32_3"] = "f3800e50Qdm?|f3800e10Gdm?",-- (64-imm6) at 16-- (64-imm6) at 16
  ["vrev16._2"] = "f3b00140Qdmi|f3b00100Gdmi",
  ["vrev32._2"] = "f3b000c0Qdmi|f3b00080Gdmi",
  ["vrev64._2"] = "f3b00040Qdmi|f3b00000Gdmi",
  ["vpaddl.s_2"] = "f3b00240Qdmi|f3b00200Gdmi",
  ["vpaddl.u_2"] = "f3b002c0Qdmi|f3b00280Gdmi",
  ["vcls.s_2"] = "f3b00440Qdmi|f3b00400Gdmi",
  ["vclz.i_2"] = "f3b004c0Qdmi|f3b00440Gdmi",
  ["vcnt.8_2"] = "f3b00540Qdm|f3b00500Gdm",
  vmvn_2 = "f3b005c0Qdm|f3b00580Gdm",
  ["vpadal.s_2"] = "f3b00640Qdmi|f3b00600Gdmi",
  ["vpadal.u_2"] = "f3b006c0Qdmi|f3b00680Gdmi",
  ["vqabs.s_2"] = "f3b00740Qdmi|f3b00700Gdmi",
  ["vqneg.s_2"] = "f3b007c0Qdmi|f3b00780Gdmi",
  ["vcgt.s_2"] = "f3b10040Qdmi|f3b10000Gdmi",
  ["vcgt.f32_2"] = "f3b90440Qdm|f3b90400Gdm",
  ["vcge.s_2"] = "f3b100c0Qdmi|f3b10080Gdmi",
  ["vcge.f32_2"] = "f3b904c0Qdm|f3b90480Gdm",
  ["vceq.s_2"] = "f3b10140Qdmi|f3b10100Gdmi",
  ["vceq.f32_2"] = "f3b90540Qdm|f3b90500Gdm",
  ["vcle.s_2"] = "f3b101c0Qdmi|f3b10180Gdmi",
  ["vcle.f32_2"] = "f3b905c0Qdm|f3b90580Gdm",
  ["vclt.s_2"] = "f3b10240Qdmi|f3b10200Gdmi",
  ["vclt.f32_2"] = "f3b90640Qdm|f3b90600Gdm",
  ["vabs.s_2"] = "f3b10340Qdmi|f3b10300Gdmi",
  ["vabs.f32_2"] = "f3b90740Qdm|f3b90700Gdm|eeb00ac0dm",
  ["vneg.s_2"] = "f3b103c0Qdmi|f3b10380Gdmi",
  ["vneg.f32_2"] = "f3b907c0Qdm|f3b90780Gdm|eeb10a40dm",
  vswp_2 = "f3b20040Qdm|f3b20000Gdm",
  ["vtrn._2"] = "f3b200c0Qdmi|f3b20080Gdmi",
  ["vuzp._2"] = "f3b20140Qdmi|f3b20100Gdmi",
  ["vzip._2"] = "f3b201c0Qdmi|f3b20180Gdmi",
  ["vmovn.i16_2"] = "f3b20200GdQm",
  ["vmovn.i32_2"] = "f3b60200GdQm",
  ["vmovn.i64_2"] = "f3ba0200GdQm",
  ["vqmovn.s_2"] = "f3b20280GdQm?", -- p but different
  ["vqmovn.u_2"] = "f3b202c0GdQm?", -- p but different
  ["vqmovun.s_2"] = "f3b20240GdQm?",-- p but different
  ["vcvt.f32.f16_2"] = "f3b60700QdGm",
  ["vcvt.f16.f32_2"] = "f3b60600GdQm",
  ["vrecpe.u32_2"] = "f3bb0440Qdm|f3bb0400Gdm",
  ["vrecpe.f32_2"] = "f3bb0540Qdm|f3bb0500Gdm",
  ["vsqrte.u32_2"] = "f3bb04c0Qdm|f3bb0480Gdm",
  ["vsqrte.f32_2"] = "f3bb05c0Qdm|f3bb0580Gdm",
  ["vcvt.s32.f32_2"] = "f3bb0740Qdm|f3bb0700Gdm|eebd0ac0dm",
  ["vcvt.u32.f32_2"] = "f3bb07c0Qdm|f3bb0780Gdm|eebc0ac0dm",
  ["vcvt.f32.s32_2"] = "f3bb0640Qdm|f3bb0600Gdm|eeb80ac0dm",
  ["vcvt.f32.u32_2"] = "f3bb06c0Qdm|f3bb0680Gdm|eeb80a40dm",
  ["vld1._2"] = "f42000001aI|f4a000001bO|f4a00c001cI",
  ["vld1._3"] = "f42000001aI|f4a000001bO|f4a00c001cI",
  ["vld1.64_2"] = "f42000c01a",
  ["vld1.64_3"] = "f42000c01a",
  ["vld2._2"] = "f42000002aI|f4a001002bO|f4a00d002cI",
  ["vld2._3"] = "f42000002aI|f4a001002bO|f4a00d002cI",
  ["vld3._2"] = "f42000003aI|f4a002003bO|f4a00e003cI",
  ["vld3._3"] = "f42000003aI|f4a002003bO|f4a00e003cI",
  ["vld4._2"] = "f42000004aI|f4a003004bO|f4a00f004cI",
  ["vld4._3"] = "f42000004aI|f4a003004bO|f4a00f004cI",
  ["vst1._2"] = "f42000001aI|f4a000001bO",
  ["vst1._3"] = "f42000001aI|f4a000001bO",
  ["vst1.64_2"] = "f42000c01a",
  ["vst1.64_3"] = "f42000c01a",
  ["vst2._2"] = "f42000002aI|f4a001002bO",
  ["vst2._3"] = "f42000002aI|f4a001002bO",
  ["vst3._2"] = "f42000003aI|f4a002003bO",
  ["vst3._3"] = "f42000003aI|f4a002003bO",
  ["vst4._2"] = "f42000004aI|f4a003004bO",
  ["vst4._3"] = "f42000004aI|f4a003004bO",



  -- NYI: I have no need for these instructions right now:
  -- swp, swpb, strex, ldrex, strexd, ldrexd, strexb, ldrexb, strexh, ldrexh
  -- msr, nopv6, yield, wfe, wfi, sev, dbg, bxj, smc, srs, rfe
  -- cps, setend, pli, pld, pldw, clrex, dsb, dmb, isb
  -- stc, ldc, mcr, mcr2, mrc, mrc2, mcrr, mcrr2, mrrc, mrrc2, cdp, cdp2
}


local function tappend(t, k, v)
  if t[k] then
    t[k] = t[k].."|"..v
  else
    t[k] = v
  end
end

-- Add mnemonics for variants.
do
  local t = {}
  for k,v in pairs(map_op) do
    local entries = {}
    for s in gmatch(v, "([^|]+)") do entries[#entries + 1] = s end
    for i, v in ipairs(entries) do
      local lastchar = sub(v, -1)
      -- replacements
      if lastchar == "U" then  -- variants: s8/s16/s32/u8/u16/u32 @ bit 20
        tappend(t, sub(k, 1, -3).."s8"..sub(k, -2), sub(v, 1, 2)..char(byte(v, 3)+0)..sub(v, 4, -2))
        tappend(t, sub(k, 1, -3).."s16"..sub(k, -2), sub(v, 1, 2)..char(byte(v, 3)+1)..sub(v, 4, -2))
        tappend(t, sub(k, 1, -3).."s32"..sub(k, -2), sub(v, 1, 2)..char(byte(v, 3)+2)..sub(v, 4, -2))
        tappend(t, sub(k, 1, -3).."u8"..sub(k, -2), sub(v, 1, 1)..char(byte(v, 2)+1)..char(byte(v, 3)+0)..sub(v, 4, -2))
        tappend(t, sub(k, 1, -3).."u16"..sub(k, -2), sub(v, 1, 1)..char(byte(v, 2)+1)..char(byte(v, 3)+1)..sub(v, 4, -2))
        tappend(t, sub(k, 1, -3).."u32"..sub(k, -2), sub(v, 1, 1)..char(byte(v, 2)+1)..char(byte(v, 3)+2)..sub(v, 4, -2))
      elseif lastchar == "u" then  -- variants: 8/16/32 @ bit 20
        tappend(t, sub(k, 1, -3).."8"..sub(k, -2), sub(v, 1, 2)..char(byte(v, 3)+0)..sub(v, 4, -2))
        tappend(t, sub(k, 1, -3).."16"..sub(k, -2), sub(v, 1, 2)..char(byte(v, 3)+1)..sub(v, 4, -2))
        tappend(t, sub(k, 1, -3).."32"..sub(k, -2), sub(v, 1, 2)..char(byte(v, 3)+2)..sub(v, 4, -2))
      elseif lastchar == "i" then  -- variants: 8/16/32 @ bit 18
        tappend(t, sub(k, 1, -3).."8"..sub(k, -2), sub(v, 1, 3)..char(byte(v, 4)+0)..sub(v, 5, -2))
        tappend(t, sub(k, 1, -3).."16"..sub(k, -2), sub(v, 1, 3)..char(byte(v, 4)+4)..sub(v, 5, -2))
        tappend(t, sub(k, 1, -3).."32"..sub(k, -2), sub(v, 1, 3)..char(byte(v, 4)+8)..sub(v, 5, -2))
      elseif lastchar == "I" then  -- variants: 8/16/32 @ bit 6
        tappend(t, sub(k, 1, -3).."8"..sub(k, -2), sub(v, 1, 6)..char(byte(v, 7)+0)..sub(v, 8, -2))
        tappend(t, sub(k, 1, -3).."16"..sub(k, -2), sub(v, 1, 6)..char(byte(v, 7)+4)..sub(v, 8, -2))
        tappend(t, sub(k, 1, -3).."32"..sub(k, -2), sub(v, 1, 6)..char(byte(v, 7)+8)..sub(v, 8, -2))
      elseif lastchar == "O" then  -- variants: 8/16/32 @ bit 10
        tappend(t, sub(k, 1, -3).."8"..sub(k, -2), sub(v, 1, 5)..char(byte(v, 6)+0)..sub(v, 7, -2))
        tappend(t, sub(k, 1, -3).."16"..sub(k, -2), sub(v, 1, 5)..char(byte(v, 6)+4)..sub(v, 7, -2))
        tappend(t, sub(k, 1, -3).."32"..sub(k, -2), sub(v, 1, 5)..char(byte(v, 6)+8)..sub(v, 7, -2))
      else
        -- original
        tappend(t, k, v)
        -- additions
        if lastchar == "s" then
          local v2 = sub(v, 1, 2)..char(byte(v, 3)+1)..sub(v, 4, -2)
          tappend(t, sub(k, 1, -3).."s"..sub(k, -2), v2)
        end
      end
    end
  end
  for k,v in pairs(map_op) do
    map_op[k] = nil
  end
  for k,v in pairs(t) do
    map_op[k] = v
  end
end

------------------------------------------------------------------------------

local function parse_gpr(expr, shift, nodefer)
  local tname, ovreg = match(expr, "^([%w_]+):(r%(?1?[0-9]%)?)$")
  local tp = map_type[tname or expr]
  if tp then
    local reg = ovreg or tp.reg
    if not reg then
      werror("type `"..(tname or expr).."' needs a register override")
    end
    expr = reg
  end
  local r = match(expr, "^r(1?[0-9])$")
  if r then
    r = tonumber(r)
    if r <= 15 then return shl(r, shift), tp end
  end
  if not nodefer then
    local rv = match(expr, "^r%(([^)]+)%)$")
    if rv then
      -- store as action to read later
      wimmaction(rv, 0, 4, shift, false)
      return 0, tp
    end
  end
  werror("bad register name `"..expr.."'")
end

local function parse_gpr_pm(expr, shift)
  local pm, expr2 = match(expr, "^([+-]?)(.*)$")
  return parse_gpr(expr2, shift), (pm == "-")
end

local function parse_vr(expr, tp, rp, hp)
  local t, r = match(expr, "^([sdq])([0-9]+)$")
  if t == tp then
    r = tonumber(r)
    if t == "q" then r = r * 2 end
    if r <= 31 then
      if t == "s" then return shl(shr(r, 1), rp) + shl(band(r, 1), hp) end
      return shl(band(r, 15), rp) + shl(shr(r, 4), hp)
    end
  end
  local tv, rv = match(expr, "^([sdq])%(([^)]+)%)$")
  if tv == tp then
    -- store as action to read later
    if tv == "s" then
      wimmaction(rv, 1, 4, rp, false)
      wimmaction(rv, 0, 1, hp, false)
    elseif tv == "d" then
      wimmaction(rv, 0, 4, rp, false)
      wimmaction(rv, 4, 1, hp, false)
    elseif tv == "q" then
      -- hack: push everything up by 1 bit to double it (q --> d)
      wimmaction(rv, 0, 3, rp+1, false)
      wimmaction(rv, 3, 1, hp, false)
    else
      werror("invalid register type detected: "..tv)
    end
    return 0
  end
  werror("bad register name `"..expr.."'")
end

local function parse_reglist(reglist)
  reglist = match(reglist, "^{%s*([^}]*)}$")
  if not reglist then werror("register list expected") end
  local rr = 0
  for p in gmatch(reglist..",", "%s*([^,]*),") do
    -- check if we have a literal GPR
    local m = match(p, "^[%w_]*:?r(1?[0-9])$")
    if m then
      local rbit = shl(1, tonumber(m))
      if band(rr, rbit) ~= 0 then
        werror("duplicate register `"..p.."'")
      end
      rr = bor(rr, rbit)
    else
      local mv = match(p, "^r%(([^)]+)%)$")
      if mv then
        waction("IMMSHIFT", 1, mv)
        -- rr = rr + 0
      else
        werror("invalid register signature")
      end
    end
  end
  return rr
end

local function parse_vrlist(reglist)
  local ta, ras, tb, rbs = match(reglist,
                           "^{%s*([sd])([0-9]+)%s*%-%s*([sd])([0-9]+)%s*}$")
  if not ras or not rbs then
    ta, ras, tb, rbs = match(reglist,
                           "^{%s*([sd])%(([^)-]+)%)%s*%-%s*([sd])%(([^)]+)%)%s*}$")
  end
  ra, rb = tonumber(ras), tonumber(rbs)
  if ta and ta == tb and ra and rb then
    if ra <= 31 and rb <= 31 and ra <= rb then
      local nr = rb+1 - ra
      if ta == "s" then
        return shl(shr(ra,1),12)+shl(band(ra,1),22) + nr
      else
        return shl(band(ra,15),12)+shl(shr(ra,4),22) + nr*2 + 0x100
      end
    end
  elseif ta and ta == tb and ras and rbs then
    waction2("VRLIST", (ta == "d" and 1 or 0), ras, rbs)
    return 0
  end
  werror("register list expected")
end

local function parse_imm_n(imm, bits, shift, scale, allowlossy, allowoor)
  local n = tonumber(imm)
  if n then
    local m = sar(n, scale)
    if allowlossy or shl(m, scale) == n then
      if allowoor then m = band(m, shl(1, bits)-1) end
      if sar(m, bits) == 0 then return shl(m, shift) end
    end
    werror("out of range immediate `"..imm.."'")
  else
    wimmaction(imm, scale, bits, shift)
    return 0
  end
end

local function parse_imm(imm, bits, shift, scale, allowlossy, allowoor)
  imm = match(imm, "^#(.*)$")
  if not imm then werror("expected immediate operand") end
  return parse_imm_n(imm, bits, shift, scale, allowlossy, allowoor)
end

local function parse_immo_n(imm, offset, bits, shift, allowoor)
  local m = tonumber(imm)
  if m then
    m = m + offset
    if allowoor then m = band(m, shl(1, bits)-1) end
    if sar(m, bits) == 0 then return shl(m, shift) end
    werror("out of range immediate `"..imm.."'")
  else
    if offset >= -15 and offset <= 15 then
      if offset < 0 then offset = 16 - offset end
      wimmaction(imm, offset, bits, shift, true)
      return 0
    end
    werror("out of range offset `"..offset.."'")
  end
end

local function parse_immo(imm, offset, bits, shift, allowoor)
  imm = match(imm, "^#(.*)$")
  if not imm then werror("expected immediate operand") end
  return parse_immo_n(imm, offset, bits, shift, allowoor)
end

local function parse_imm12(imm)
  local n = tonumber(imm)
  if n then
    local m = band(n)
    for i=0,-15,-1 do
      if shr(m, 8) == 0 then return m + shl(band(i, 15), 8) end
      m = ror(m, 2)
    end
    werror("out of range immediate `"..imm.."'")
  else
    waction("IMM12", 0, imm)
    return 0
  end
end

local function parse_imm16(imm)
  imm = match(imm, "^#(.*)$")
  if not imm then werror("expected immediate operand") end
  local n = tonumber(imm)
  if n then
    if shr(n, 16) == 0 then return band(n, 0x0fff) + shl(band(n, 0xf000), 4) end
    werror("out of range immediate `"..imm.."'")
  else
    waction("IMM16", 32*16, imm)
    return 0
  end
end

local function parse_imm_load(imm, ext)
  local n = tonumber(imm)
  if n then
    if ext then
      if n >= -255 and n <= 255 then
        local up = 0x00800000
        if n < 0 then n = -n; up = 0 end
        return shl(band(n, 0xf0), 4) + band(n, 0x0f) + up
      end
    else
      if n >= -4095 and n <= 4095 then
        if n >= 0 then return n+0x00800000 end
        return -n
      end
    end
    werror("out of range immediate `"..imm.."'")
  else
    waction(ext and "IMML8" or "IMML12", 32768 + shl(ext and 8 or 12, 5), imm)
    return 0
  end
end

local function parse_shift(shift, gprok)
  if shift == "rrx" then
    return 3 * 32
  else
    local s, s2 = match(shift, "^(%S+)%s*(.*)$")
    s = map_shift[s]
    if not s then werror("expected shift operand") end
    if sub(s2, 1, 1) == "#" then
      return parse_imm(s2, 5, 7, 0) + shl(s, 5)
    else
      if not gprok then werror("expected immediate shift operand") end
      return parse_gpr(s2, 8) + shl(s, 5) + 16
    end
  end
end

local function parse_label(label, def, pbase)
  local prefix = sub(label, 1, 2)
  local base = pbase and pbase or 0
  -- =>label (pc label reference)
  if prefix == "=>" then
    return "PC", 0, sub(label, 3)
  end
  -- ->name (global label reference)
  if prefix == "->" then
    return "LG", map_global[sub(label, 3)] + base
  end
  if def then
    -- [1-9] (local label definition)
    if match(label, "^[1-9]$") then
      return "LG", 10+tonumber(label) + base
    end
  else
    -- [<>][1-9] (local label reference)
    local dir, lnum = match(label, "^([<>])([1-9])$")
    if dir then -- Fwd: 1-9, Bkwd: 11-19.
      return "LG", lnum + (dir == ">" and 0 or 10) + base
    end
    -- extern label (extern label reference)
    local extname = match(label, "^extern%s+(%S+)$")
    if extname then
      return "EXT", map_extern[extname] + base
    end
    local ptrname = match(label, "^ptr%s+(.+)$")
    if ptrname then
      return "APC", base, "(int)("..ptrname..")"
    end
  end
  werror("bad label `"..label.."'")
end

local function parse_load(params, nparams, n, op)
  local oplo = band(op, 255)
  local ext = (oplo ~= 0)
  local pn = params[n]
  local p1, wb = match(pn, "^%[%s*(.-)%s*%](!?)$")
  local p2 = params[n+1]
  if not p1 then
    if not p2 then
      -- label?
      if match(pn, "^[<>=%-]") or match(pn, "^extern%s+") or match(pn, "^ptr%s+") then
        local mode, n, s = parse_label(pn, false)
        waction("REL_"..mode, n + (ext and 0x1800 or 0x0800), s, 1)
        -- LIT: op + (1111 -> Rn)
        return op + 15 * 65536 + 0x01000000 + (ext and 0x00400000 or 0)
      end
      -- GPR?
      local reg, tailr = match(pn, "^([%w_:]+)%s*(.*)$")
      if reg and tailr ~= "" then
        local d, tp = parse_gpr(reg, 16)
        if tp then
          waction(ext and "IMML8" or "IMML12", 32768 + 32*(ext and 8 or 12),
                  format(tp.ctypefmt, tailr))
          -- IMM1/2: op + (d -> Rn)
          return op + d + 0x01000000 + (ext and 0x00400000 or 0)
        end
      end
    end
    werror("expected address operand")
  end
  if wb == "!" then op = op + 0x00200000 end
  if p2 then
    -- IMM1/2
    if wb == "!" then werror("bad use of '!'") end
    local p3 = params[n+2]
    op = op + parse_gpr(p1, 16)
    local imm = match(p2, "^#(.*)$")
    if imm then
      local m = parse_imm_load(imm, ext)
      if p3 then werror("too many parameters") end
      op = op + m + (ext and 0x00400000 or 0)
    else
      local m, neg = parse_gpr_pm(p2, 0)
      op = op + m + (neg and 0 or 0x00800000) + (ext and 0 or 0x02000000)
      if p3 then op = op + parse_shift(p3) end
    end
  else
    local p1a, p2 = match(p1, "^([^,%s]*)%s*(.*)$")
    op = op + parse_gpr(p1a, 16) + 0x01000000
    if p2 ~= "" then
      local imm = match(p2, "^,%s*#(.*)$")
      if imm then
        -- IMM1/2
        local m = parse_imm_load(imm, ext)
        op = op + m + (ext and 0x00400000 or 0)
      else
        -- REG
        local p2a, p3 = match(p2, "^,%s*([^,%s]*)%s*,?%s*(.*)$")
        local m, neg = parse_gpr_pm(p2a, 0)
        op = op + m + (neg and 0 or 0x00800000) + (ext and 0 or 0x02000000)
        if p3 ~= "" then
          if ext then werror("too many parameters") end
          op = op + parse_shift(p3)
        end
      end
    else
      if wb == "!" then werror("bad use of '!'") end
      op = op + (ext and 0x00c00000 or 0x00800000)
    end
  end
  return op
end

local function parse_vload(q)
  local reg, imm = match(q, "^%[%s*([^,%s]*)%s*(.*)%]$")
  if reg then
    local d = parse_gpr(reg, 16)
    if imm == "" then return d end
    imm = match(imm, "^,%s*#(.*)$")
    if imm then
      local n = tonumber(imm)
      if n then
        if n >= -1020 and n <= 1020 and n%4 == 0 then
          return d + (n >= 0 and n/4+0x00800000 or -n/4)
        end
        werror("out of range immediate `"..imm.."'")
      else
        waction("IMMV8", 32768 + 32*8, imm)
        return d
      end
    end
  else
    if match(q, "^[<>=%-]") or match(q, "^extern%s+") then
      local mode, n, s = parse_label(q, false)
      waction("REL_"..mode, n + 0x2800, s, 1)
      return 15 * 65536
    end
    local reg, tailr = match(q, "^([%w_:]+)%s*(.*)$")
    if reg and tailr ~= "" then
      local d, tp = parse_gpr(reg, 16)
      if tp then
        waction("IMMV8", 32768 + 32*8, format(tp.ctypefmt, tailr))
        return d
      end
    end
  end
  werror("expected address operand")
end

local function parse_srload_common(q, r)
  local reglist = match(q, "^%s*{%s*([^}]+)%s*}%s*")
  if not reglist then
    werror("expected at least a NEON register list and a GPR")
  end
  local align = 0
  local full1, rn = match(r, "^(%s*%[(r[^%]:]+))")
  local alignstr, wb = match(sub(r, #full1 + 1), "^:([0-9]+)%s*%](!?)%s*$")
  if alignstr then
    align = tonumber(alignstr)
  else
    full1, wb = match(sub(r, #full1 + 1), "^(%s*%](!?)%s*)$")
    if not full1 then
      werror("unclosed address specifier")
    end
  end
  return reglist, rn, align, wb
end

local function parse_srload_reglist(l, mode)
  local indexlist = nil
  -- range?
  local r1t, r1ns, r1is, r2t, r2ns, r2is = match(l, "^([dq])([0-9]+)([^%s]*)%s*-%s*([dq])([0-9]+)([^%s]*)$")
  if not r1t or not r1ns or not r2t or not r2ns then
    r1t, r1ns, r1is, r2t, r2ns, r2is = match(l, "^([dq])%((.-)%)([^%s]*)%s*-%s*([dq])%((.-)%)([^%s]*)$")
  end
  if r1is and #r1is == 0 then r1is = nil end
  if r2is and #r2is == 0 then r2is = nil end
  if r1t and r1ns and r2t and r2ns then
    if r1t ~= r2t then werror("all entries in NEON register range must be of the same type") end
    if mode == "a" and (r1is or r2is) then
      werror("invalid NEON register range for this instruction variant") end
    if mode == "c" and (not r1is or not r2is or r1is ~= "[]" or r2is ~= "[]") then
      werror("invalid NEON register range for this instruction variant")
    end
    if mode == "b" then
      if not r1is or not r2is then werror("invalid NEON register range for this instruction variant") end
      r1is = match(r1is, "^%[([^%]]+)%]$")
      r2is = match(r2is, "^%[([^%]]+)%]$")
      if not r1is or not r2is then werror("could not parse NEON register indices") end
      indexlist = {r1is, r2is}
    end
    return r1t, {r1ns, r2ns}, indexlist, true
  end
  -- list?
  local rlist = {}
  if mode == "b" then indexlist = {} end
  for str in gmatch(l, "([^,]+)") do rlist[#rlist + 1] = str end
  if #rlist == 0 then werror("expected NEON register list or range") end
  local regtype = match(rlist[1], "^%s*([dq])[^%s]+%s*$")
  if not regtype then werror("could not parse NEON register list") end
  for i,v in ipairs(rlist) do
    r1t = match(v, "^%s*([dq])[^%s]+%s*$")
    if not r1t then werror("could not parse NEON register list") end
    if regtype ~= r1t then werror("all entries in NEON register list must be of the same type") end
  end
  for i=1,#rlist do
    local rl, ris = match(rlist[i], "^%s*[dq]([0-9]+)([^%s]*)%s*$")
    if not rl then
      rl, ris = match(rlist[i], "^%s*[dq]%((.-)%)([^%s]*)%s*$")
    end
    if not rl then werror("could not parse NEON register list") end
    if mode == "a" and ris and #ris ~= 0 then werror("invalid NEON register for this instruction variant") end
    if mode == "c" and (not ris or ris ~= "[]") then werror("invalid NEON register for this instruction variant") end
    rlist[i] = rl
    if mode == "b" then
      if not ris then werror("invalid NEON register list for this instruction variant") end
      ris = match(ris, "^%[([^%]]+)%]$")
      if not ris then werror("could not parse NEON register indices") end
      indexlist[i] = ris
    end
  end
  return regtype, rlist, indexlist, false
end

local function parse_srload(params, nparams, n, op, vldn, mode)
  local size = band(shr(op, mode == "b" and 10 or 6), 0x3)
  local reglstr, rns, align, wb = parse_srload_common(params[n], params[n+1])
  local srtype, srlist, indexlist, isrange = parse_srload_reglist(reglstr, mode)

  if srtype == "q" and mode == "c" then
    werror("cannot perform NEON all-lane load/store on quad register")
  end

  local opadd = 0
  opadd = opadd + parse_gpr(rns, 16)
  if n + 2 <= #params then
    opadd = opadd + parse_gpr(params[n+2], 0)
  else
    opadd = opadd + ((wb and wb == "!") and 0xD or 0xF)
  end

  if (not isrange) and vldn ~= #srlist then
    if mode == "a" and (vldn == 1 or (vldn == 2 and #srlist == 4)) then
      -- OK
    elseif mode == "c" and vldn == 1 and #srlist == 2 then
      -- OK
    else
      werror("invalid register count in register list")
    end
  end

  -- TODO: check if alignment is valid, and add it to opadd as appropriate

  if indexlist then
    for i=1, #indexlist do
      srlist[#srlist+1] = indexlist[i]
    end
  end

  local actval = band(vldn - 1, 0x3)
  actval = bor(actval, shl(band(size, 0x3), 2))
  actval = bor(actval, shl(band(byte(mode) - byte("a"), 0x3), 4))
  actval = bor(actval, shl(isrange and 0x1 or 0x0, 6))
  actval = bor(actval, shl(srtype == "q" and 0x1 or 0x0, 7))
  actval = bor(actval, shl(band(#srlist, 0xF), 8))

  wactionn("SRLIST", actval, srlist)
  return opadd
end

------------------------------------------------------------------------------

-- Handle opcodes defined with template strings.
local function parse_template(params, template, nparams, pos)
  local op = tonumber(sub(template, 1, 8), 16)
  local n = 1
  local vr = "s"
  local vldn = 1

  -- Process each character.
  for p in gmatch(sub(template, 9), ".") do
    local q = params[n]
    if p == "D" then
      op = op + parse_gpr(q, 12); n = n + 1
    elseif p == "N" then
      op = op + parse_gpr(q, 16); n = n + 1
    elseif p == "S" then
      op = op + parse_gpr(q, 8); n = n + 1
    elseif p == "M" then
      op = op + parse_gpr(q, 0); n = n + 1
    elseif p == "d" then
      op = op + parse_vr(q, vr, 12, 22); n = n + 1
    elseif p == "n" then
      op = op + parse_vr(q, vr, 16, 7); n = n + 1
    elseif p == "m" then
      op = op + parse_vr(q, vr, 0, 5); n = n + 1
    elseif p == "z" then  -- m, and m in the n slot also
      op = op + parse_vr(q, vr, 0, 5) + parse_vr(q, vr, 16, 7); n = n + 1
    --elseif p == "j" then
    --  op = op + parse_sr_index(...)
    elseif p == "P" then
      local imm = match(q, "^#(.*)$")
      if imm then
        op = op + parse_imm12(imm) + 0x02000000
      else
        op = op + parse_gpr(q, 0)
      end
      n = n + 1
    elseif p == "p" then
      op = op + parse_shift(q, true); n = n + 1
    elseif p == "L" then
      op = parse_load(params, nparams, n, op)
    elseif p == "l" then
      op = op + parse_vload(q)
    elseif p == "B" then
      local mode, n, s = parse_label(q, false, 0)
      waction("REL_"..mode, n, s, 1)
    elseif p == "C" then -- blx gpr vs. blx label.
      if match(q, "^([%w_]+):(r1?[0-9])$") or match(q, "^r(1?[0-9])$") then
        op = op + parse_gpr(q, 0)
      else
        if op < 0xe0000000 then werror("unconditional instruction") end
        local mode, n, s = parse_label(q, false)
        waction("REL_"..mode, n, s, 1)
        op = 0xfa000000
      end
    elseif p == "F" then
      vr = "s"
    elseif p == "G" then
      vr = "d"
    elseif p == "Q" then
      vr = "q"
    elseif p == "o" then
      local r, wb = match(q, "^([^!]*)(!?)$")
      op = op + parse_gpr(r, 16) + (wb == "!" and 0x00200000 or 0)
      n = n + 1
    elseif p == "R" then
      op = op + parse_reglist(q); n = n + 1
    elseif p == "r" then
      op = op + parse_vrlist(q); n = n + 1
    elseif p == "W" then
      op = op + parse_imm16(q); n = n + 1
    elseif p == "v" then
      op = op + parse_imm(q, 5, 7, 0); n = n + 1
    elseif p == "t" then
      op = op + parse_immo(q, -1, 5, 16, false); n = n + 1
    elseif p == "w" then
      local imm = match(q, "^#(.*)$")
      if imm then
        op = op + parse_imm(q, 5, 7, 0); n = n + 1
      else
        op = op + parse_gpr(q, 8) + 16
      end
    elseif p == "X" then
      op = op + parse_imm(q, 5, 16, 0); n = n + 1
    elseif p == "Y" then
      local imm = tonumber(match(q, "^#(.*)$")); n = n + 1
      if not imm or shr(imm, 8) ~= 0 then
        werror("bad immediate operand")
      end
      op = op + shl(band(imm, 0xf0), 12) + band(imm, 0x0f)
    elseif p == "K" then
      local imm = tonumber(match(q, "^#(.*)$")); n = n + 1
      if not imm or shr(imm, 16) ~= 0 then
        werror("bad immediate operand")
      end
      op = op + shl(band(imm, 0xfff0), 4) + band(imm, 0x000f)
    elseif p == "T" then
      op = op + parse_imm(q, 24, 0, 0); n = n + 1
    elseif p == "1" or p == "2" or p == "3" or p == "4" then
      vldn = tonumber(p)
    elseif p == "a" or p == "b" or p == "c" then
      op = op + parse_srload(params, nparams, n, op, vldn, p); n = n + 1
    elseif string.find("sUuIiO", p) then
      -- Ignored.
    else
      assert(false)
    end
  end
  wputpos(pos, op)
end

map_op[".template__"] = function(params, template, nparams)
  if not params then return template:gsub("%x%x%x%x%x%x%x%x", "") end

  -- Limit number of section buffer positions used by a single dasm_put().
  -- A single opcode needs a maximum of 3 positions.
  if secpos+3 > maxsecpos then wflush() end
  local pos = wpos()
  local lpos, apos, spos = #actlist, #actargs, secpos

  local ok, err
  for t in gmatch(template, "[^|]+") do
    ok, err = pcall(parse_template, params, t, nparams, pos)
    if ok then return end
    secpos = spos
    actlist[lpos+1] = nil
    actlist[lpos+2] = nil
    actlist[lpos+3] = nil
    actargs[apos+1] = nil
    actargs[apos+2] = nil
    actargs[apos+3] = nil
  end
  error(err, 0)
end

------------------------------------------------------------------------------

-- Pseudo-opcode to mark the position where the action list is to be emitted.
map_op[".actionlist_1"] = function(params)
  if not params then return "cvar" end
  local name = params[1] -- No syntax check. You get to keep the pieces.
  wline(function(out) writeactions(out, name) end)
end

-- Pseudo-opcode to mark the position where the global enum is to be emitted.
map_op[".globals_1"] = function(params)
  if not params then return "prefix" end
  local prefix = params[1] -- No syntax check. You get to keep the pieces.
  wline(function(out) writeglobals(out, prefix) end)
end

-- Pseudo-opcode to mark the position where the global names are to be emitted.
map_op[".globalnames_1"] = function(params)
  if not params then return "cvar" end
  local name = params[1] -- No syntax check. You get to keep the pieces.
  wline(function(out) writeglobalnames(out, name) end)
end

-- Pseudo-opcode to mark the position where the extern names are to be emitted.
map_op[".externnames_1"] = function(params)
  if not params then return "cvar" end
  local name = params[1] -- No syntax check. You get to keep the pieces.
  wline(function(out) writeexternnames(out, name) end)
end

------------------------------------------------------------------------------

-- Label pseudo-opcode (converted from trailing colon form).
map_op[".label_1"] = function(params)
  if not params then return "[1-9] | ->global | =>pcexpr" end
  if secpos+1 > maxsecpos then wflush() end
  local mode, n, s = parse_label(params[1], true)
  if mode == "EXT" then werror("bad label definition") end
  waction("LABEL_"..mode, n, s, 1)
end

------------------------------------------------------------------------------

-- Pseudo-opcodes for data storage.
map_op[".long_*"] = function(params)
  if not params then return "imm..." end
  for _,p in ipairs(params) do
    local n = tonumber(p)
    if n then
      if n < 0 then n = n + 2^32 end
      wputw(n)
    else
      pstr = "(int)("..p..")"
      wputw(0)
      waction("IMM32", 0, pstr)
    end
    if secpos+2 > maxsecpos then wflush() end
  end
end

-- Alignment pseudo-opcode.
map_op[".align_1"] = function(params)
  if not params then return "numpow2" end
  if secpos+1 > maxsecpos then wflush() end
  local align = tonumber(params[1])
  if align then
    local x = align
    -- Must be a power of 2 in the range (2 ... 256).
    for i=1,8 do
      x = x / 2
      if x == 1 then
        waction("ALIGN", align-1, nil, 1) -- Action byte is 2**n-1.
        return
      end
    end
  end
  werror("bad alignment")
end

------------------------------------------------------------------------------

-- Pseudo-opcode for (primitive) type definitions (map to C types).
map_op[".type_3"] = function(params, nparams)
  if not params then
    return nparams == 2 and "name, ctype" or "name, ctype, reg"
  end
  local name, ctype, reg = params[1], params[2], params[3]
  if not match(name, "^[%a_][%w_]*$") then
    werror("bad type name `"..name.."'")
  end
  local tp = map_type[name]
  if tp then
    werror("duplicate type `"..name.."'")
  end
  -- Add #type to defines. A bit unclean to put it in map_archdef.
  map_archdef["#"..name] = "sizeof("..ctype..")"
  -- Add new type and emit shortcut define.
  local num = ctypenum + 1
  map_type[name] = {
    ctype = ctype,
    ctypefmt = format("Dt%X(%%s)", num),
    reg = reg,
  }
  wline(format("#define Dt%X(_V) (int)(ptrdiff_t)&(((%s *)0)_V)", num, ctype))
  ctypenum = num
end
map_op[".type_2"] = map_op[".type_3"]

-- Dump type definitions.
local function dumptypes(out, lvl)
  local t = {}
  for name in pairs(map_type) do t[#t+1] = name end
  sort(t)
  out:write("Type definitions:\n")
  for _,name in ipairs(t) do
    local tp = map_type[name]
    local reg = tp.reg or ""
    out:write(format("  %-20s %-20s %s\n", name, tp.ctype, reg))
  end
  out:write("\n")
end

------------------------------------------------------------------------------

-- Set the current section.
function _M.section(num)
  waction("SECTION", num)
  wflush(true) -- SECTION is a terminal action.
end

------------------------------------------------------------------------------

-- Dump architecture description.
function _M.dumparch(out)
  out:write(format("DynASM %s version %s, released %s\n\n",
    _info.arch, _info.version, _info.release))
  dumpactions(out)
end

-- Dump all user defined elements.
function _M.dumpdef(out, lvl)
  dumptypes(out, lvl)
  dumpglobals(out, lvl)
  dumpexterns(out, lvl)
end

------------------------------------------------------------------------------

-- Pass callbacks from/to the DynASM core.
function _M.passcb(wl, we, wf, ww)
  wline, werror, wfatal, wwarn = wl, we, wf, ww
  return wflush
end

-- Setup the arch-specific module.
function _M.setup(arch, opt)
  g_arch, g_opt = arch, opt
end

-- Merge the core maps and the arch-specific maps.
function _M.mergemaps(map_coreop, map_def)
  setmetatable(map_op, { __index = function(t, k)
    local v = map_coreop[k]
    if v then return v end
    local k1, cc, k2 = match(k, "^(.-)(..)([._].*)$")
    local cv = map_cond[cc]
    if cv then
      local v = rawget(t, k1..k2)
      if type(v) == "string" then
        local scv = format("%x", cv)
        return gsub(scv..sub(v, 2), "|e", "|"..scv)
      end
    end
  end })
  setmetatable(map_def, { __index = map_archdef })
  return map_op, map_def
end

return _M

------------------------------------------------------------------------------

