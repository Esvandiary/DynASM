------------------------------------------------------------------------------
-- DynASM ARM module.
--
-- Copyright (C) 2005-2017 Mike Pall. All rights reserved.
-- See dynasm.lua for full copyright notice.
------------------------------------------------------------------------------

-- Module information:
local _info = {
  arch =           "armv7m",
  description =    "DynASM ARMv7M module",
  version =        "1.4.0",
  vernum =         10400,
  release =        "2019-02-05",
  author =         "Mike Pall, Andy Martin",
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
local band, bor, bxor, shl, shr, sar = bit.band, bit.bor, bit.bxor, bit.lshift, bit.rshift, bit.arshift
local ror, tohex = bit.ror, bit.tohex

-- Inherited tables and callbacks.
local g_opt, g_arch
local wline, werror, wfatal, wwarn

-- Action name list.
-- CHECK: Keep this in sync with the C code!
local action_names = {
  -- 0 args
  "STOP", "SECTION", "ESC", "REL_EXT",
  "ALIGN", "REL_LG", "LABEL_LG",
  -- 1 arg
  "REL_PC", "LABEL_PC", "REL_APC",
  "IMM", "IMM12", "IMM16", "IMM32",
  "IMML", "IMMV8", "IMMSHIFT",
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

-- Put escaped word.
local function wputraw(n)
  if n <= 0x001fffff then waction("ESC") end
  actlist[#actlist+1] = n
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

function addnop(s, a)
  return s.."bf00"..a
end
local thumb_rm = 19

------------------------------------------------------------------------------

-- Template strings for ARM instructions.
local map_op = {
  adc_3 = "eb400000DNMs|f1400000DNIs",
  adc_4 = "eb400000DNMps",
  add_3 = "eb000000DNMs|f1000000DNIs",
  add_4 = "eb000000DNMps",
  addw_3 = "f2000000DNi",
  adr_2 = "f20f0000DJ",
  and_3 = "ea000000DNMs|f0000000DNIs",
  and_4 = "ea000000DNMps",
  asr_3 = "fa40f000DNMs|ea4f0020DMxs",
  b_1 = "f0009000B",
  bal_1 = "f0009000B",
  beq_1 = "f0008000b",
  bne_1 = "f0408000b",
  bcs_1 = "f0808000b",
  bcc_1 = "f0c08000b",
  bmi_1 = "f1008000b",
  bpl_1 = "f1408000b",
  bvs_1 = "f1808000b",
  bvc_1 = "f1c08000b",
  bhi_1 = "f2008000b",
  bls_1 = "f2408000b",
  bge_1 = "f2808000b",
  blt_1 = "f2c08000b",
  bgt_1 = "f3008000b",
  ble_1 = "f3408000b",
  bl_1 = "f000d000B",
  blal_1 = "f000d000B",
  blx_1 = addnop("4780","j"),
  bx_1 = addnop("4700", "j"),
  bfc_3 = "f36f0000Dz",
  bfi_4 = "f3600000DNz",
  bic_3 = "ea200000DNMs|f0200000DNIs",
  bic_4 = "ea200000DNMps",
  bkpt_1 = addnop("be00", "K"),
  -- cbz_2 = addnop("b100", "kC"),  -- TODO: would be awkward to use (NOP ordering)
  -- cbnz_2 = addnop("b900", "kC"), -- TODO: would be awkward to use (NOP ordering)
  clz_2 = "fab0f080DZ",
  cmn_2 = "eb100f00NM|f1100f00NI", -- condition flags only
  cmn_3 = "eb100f00NMp",           -- condition flags only
  cmp_2 = "ebb00f00NM|f1b00f00NI", -- condition flags only
  cmp_3 = "ebb00f00NMp",           -- condition flags only
  eor_3 = "ea800000DNMs|f0800000DNIs",
  eor_4 = "ea800000DNMps",
  ldm_2 = "e8900000oR",
  ldmdb_2 = "e9100000oR",
  ldmea_2 = "e9100000oR",
  ldr_2 = "f8500000TL",
  ldr_3 = "f8500000TL",
  ldr_4 = "f8500000TL",
  ldrb_2 = "f8100000TL",
  ldrb_3 = "f8100000TL",
  ldrb_4 = "f8100000TL",
  ldrbt_3 = "f8100e00TL",
  ldrd_3 = "e9500000TDl",
  ldrd_4 = "e9500000TDl",
  ldrh_2 = "f8300000TL",
  ldrh_3 = "f8300000TL",
  ldrht_3 = "f8300e00TL",
  ldrsb_2 = "f9100000TL",
  ldrsb_3 = "f9100000TL",
  ldrsbt_3 = "f9100e00TL",
  ldrsh_2 = "f9300000TL",
  ldrsh_3 = "f9300000TL",
  ldrsht_3 = "f9300e00TL",
  ldrt_3 = "f8500e00TL",
  lsl_3 = "fa0ff000DNMs|ea4f0000DMxs",
  lsr_3 = "fa2ff000DNMs|ea4f0010DMxs",
  mla_4 = "fb000000DNMT",
  mls_4 = "fb000010DNMT",
  mov_2 = "ea4f0000DMs|f04f0000DIs",
  movw_2 = "f2400000DW",
  movt_2 = "f2c00000DW",
  mul_3 = "fb00f000DNM",
  mvn_2 = "ea6f0000DMps|f06f0000DIs",
  neg_2 = "f1d00000DN",   -- alias for RSBS Rd, Rn, #0
  nop_0 = "bf00bf00",
  ["nop.w_0"] = "f3af8000",
  orn_3 = "ea600000DNMs|f0600000DNIs",
  orn_4 = "ea600000DNMps",
  orr_3 = "ea400000DNMs|f0400000DNIs",
  orr_4 = "ea400000DNMps",
  pkhbt_3 = "eac00000DNM",  -- v7E-M
  pkhbt_4 = "eac00000DNMx", -- v7E-M
  pkhtb_3 = "eac00020DNM",  -- v7E-M
  pkhtb_4 = "eac00020DNMx", -- v7E-M
  pop_1 = "f85d0b04T|e8bd0000R",
  push_1 = "f84d0d00T|e92d0000R",
  qadd_3 = "fa80f080DMN",   -- v7E-M
  qadd16_3 = "fa90f010DNM", -- v7E-M
  qadd8_3 = "fa80f010DNM",  -- v7E-M
  qasx_3 = "faa0f010DNM",   -- v7E-M
  qdadd_3 = "fa80f090DMN",  -- v7E-M
  qdsub_3 = "fa80f0b0DMN",  -- v7E-M
  qsax_3 = "fae0f010DNM",   -- v7E-M
  qsub_3 = "fa80f0a0DMN",   -- v7E-M
  qsub16_3 = "fad0f010DNM", -- v7E-M
  qsub8_3 = "fac0f010DNM",  -- v7E-M
  rbit_2 = "fa90f0a0DM",
  rev_2 = "fa90f080DM",
  rev16_2 = "fa90f090DM",
  revsh_2 = "fa90f0b0DM",
  ror_3 = "fa60f000DNMs|ea4f0030DMxs",
  rrx_2 = "ea4f0030DMs",
  rsb_3 = "ebc00000DNMs|f1c00000DNIs",
  rsb_4 = "ebc00000DNMps",
  sadd16_3 = "fa90f000DNM", -- v7E-M
  sadd8_3 = "fa80f000DNM",  -- v7E-M
  sasx_3 = "faa0f000DNM",   -- v7E-M
  sbc_3 = "eb600000DNMs|f1600000DNIs",
  sbc_4 = "eb600000DNMps",
  sbfx_4 = "f3400000DNz",
  sdiv_3 = "fb90f0f0DNM",
  sel_3 = "faa0f080DNM",    -- v7E-M
  shadd16_3 = "fa90f020DNM",-- v7E-M
  shadd8_3 = "fa80f020DNM", -- v7E-M
  shsax_3 = "fae0f020DNM",  -- v7E-M
  shsub16_3 = "fad0f020DNM",-- v7E-M
  shsub8_3 = "fac0f020DNM", -- v7E-M
  smlabb_4 = "fb100000DNMT",-- v7E-M
  smlabt_4 = "fb100010DNMT",-- v7E-M
  smlatb_4 = "fb100020DNMT",-- v7E-M
  smlatt_4 = "fb100030DNMT",-- v7E-M
  smlad_4 = "fb200000DNMT", -- v7E-M
  smladx_4 = "fb200010DNMT",-- v7E-M
  smlal_4 = "fbc00000TDNM",
  smlalbb_4 = "fbc00080TDNM", -- v7E-M
  smlalbt_4 = "fbc00090TDNM", -- v7E-M
  smlaltb_4 = "fbc000a0TDNM", -- v7E-M
  smlaltt_4 = "fbc000b0TDNM", -- v7E-M
  smlald_4 = "fbc000c0TDNM",  -- v7E-M
  smlaldx_4 = "fbc000d0TDNM", -- v7E-M
  smlawb_4 = "fb300000DNMT",  -- v7E-M
  smlawt_4 = "fb300010DNMT",  -- v7E-M
  smlsd_4 = "fb400000DNMT",   -- v7E-M
  smlsdx_4 = "fb400010DNMT",  -- v7E-M
  smlsld_4 = "fbd000c0TDNM",  -- v7E-M
  smlsldx_4 = "fbd000d0TDNM", -- v7E-M
  smmla_4 = "fb500000DNMT",   -- v7E-M
  smmlar_4 = "fb500010DNMT",  -- v7E-M
  smmls_4 = "fb600000DNMT",   -- v7E-M
  smmlsr_4 = "fb600010DNMT",  -- v7E-M
  smmul_3 = "fb50f000DNM",    -- v7E-M
  smmulr_3 = "fb50f010DNM",   -- v7E-M
  smuad_3 = "fb20f000DNM",    -- v7E-M
  smuadx_3 = "fb20f010DNM",   -- v7E-M
  smulbb_3 = "fb10f000DNM",   -- v7E-M
  smulbt_3 = "fb10f010DNM",   -- v7E-M
  smultb_3 = "fb10f020DNM",   -- v7E-M
  smultt_3 = "fb10f030DNM",   -- v7E-M
  smull_4 = "fb800000TDNM",
  smulwb_3 = "fb30f000DNM",   -- v7E-M
  smulwt_3 = "fb30f010DNM",   -- v7E-M
  smusd_3 = "fb40f000DNM",    -- v7E-M
  smusdx_3 = "fb40f010DNM",   -- v7E-M
  ssat_3 = "f3000000DwN",
  ssat_4 = "f3000000DwNy",
  ssat16_3 = "f3200000DwN",   -- imm is 4 bits not 5 :(
  ssax_3 = "fae0f000DNM",     -- v7E-M
  ssub16_3 = "fad0f000DNM",   -- v7E-M
  ssub8_3 = "fac0f000DNM",    -- v7E-M
  stm_2 = "e8800000oR",
  stmia_2 = "e8800000oR",
  stmea_2 = "e8800000oR",
  stmdb_2 = "e9000000oR",
  stmfd_2 = "e9000000oR",
  str_3 = "f8400000TL",
  str_4 = "f8400000TL",
  strb_3 = "f8000000TL",
  strb_4 = "f8000000TL",
  strbt_3 = "f8000e00TL",
  strd_3 = "e9400000TDl",
  strd_4 = "e9400000TDl",
  strh_2 = "f8200000TL",
  strh_3 = "f8200000TL",
  strht_2 = "f8200e00TL",
  strht_3 = "f8200e00TL",
  strt_3 = "f8400e00TL",
  sub_3 = "eba00000DNMs|f1a00000DNIs",
  sub_4 = "eba00000DNMps",
  subw_3 = "f2a00000DNi",
  sxtab_3 = "fa40f080DNM",    -- v7E-M
  sxtab_4 = "fa40f080DNMv",   -- v7E-M
  sxtab16_3 = "fa20f080DNM",  -- v7E-M
  sxtab16_4 = "fa20f080DNMv", -- v7E-M
  sxtah_3 = "fa00f080DNM",    -- v7E-M
  sxtah_4 = "fa00f080DNMv",   -- v7E-M
  sxtb_2 = "fa4ff080DM",
  sxtb_3 = "fa4ff080DMv",
  sxtb16_2 = "fa2ff080DM",    -- v7E-M
  sxtb16_3 = "fa2ff080DMv",   -- v7E-M
  sxth_2 = "fa0ff080DM",
  sxth_3 = "fa0ff080DMv",
  tbb_2 = "e8d0f000NM",
  tbh_2 = "e8d0f010NM",
  teq_2 = "ea900f00NM|f0900f00NI",  -- condition flags only
  teq_3 = "ea900f00NMI",            -- condition flags only
  tst_2 = "ea100f00NM|f0100f00NI",  -- condition flags only
  tst_3 = "ea100f00NMI",            -- condition flags only
  uadd16_3 = "fa90f040DNM", -- v7E-M
  uadd8_3 = "fa80f040DNM",  -- v7E-M
  uasx_3 = "faa0f040DNM",   -- v7E-M
  ubfx_4 = "f3c00000DNz",
  udiv_3 = "fbb0f0f0DNM",
  uhadd16_3 = "fa90f060DNM",-- v7E-M
  uhadd8_3 = "fa80f060DNM", -- v7E-M
  uhasx_3 = "faa0f060DNM",  -- v7E-M
  uhsax_3 = "fae0f060DNM",  -- v7E-M
  uhsub16_3 = "fad0f060DNM",-- v7E-M
  uhsub8_3 = "fac0f060DNM", -- v7E-M
  umaal_4 = "fbe00060TDNM", -- v7E-M
  umlal_4 = "fbe00000TDNM",
  umull_4 = "fba00000TDNM",
  uqadd16_3 = "fa90f050DNM",-- v7E-M
  uqadd8_3 = "fa80f050DNM", -- v7E-M
  uqasx_3 = "faa0f050DNM",  -- v7E-M
  uqsax_3 = "fae0f050DNM",  -- v7E-M
  uqsub16_3 = "fad0f050DNM",-- v7E-M
  uqsub8_3 = "fac0f050DNM", -- v7E-M
  usad8_3 = "fb70f000DNM",  -- v7E-M
  usada8_4 = "fb700000DNMT",-- v7E-M
  usat_3 = "f3800000DwN",
  usat_4 = "f3800000DwNy",
  usat16_3 = "f3a00000DwN", -- v7E-M, imm is actually 4 bits :(
  usax_3 = "fae0f040DNM",   -- v7E-M
  usub16_3 = "fad0f040DNM", -- v7E-M
  usub8_3 = "fac0f040DNM",  -- v7E-M
  uxtab_3 = "fa50f080DNM",   -- v7E-M
  uxtab_4 = "fa50f080DNMv",  -- v7E-M
  uxtab16_3 = "fa30f080DNM", -- v7E-M
  uxtab16_4 = "fa30f080DNMv",-- v7E-M
  uxtah_3 = "fa10f080DNM",   -- v7E-M
  uxtah_4 = "fa10f080DNMv",  -- v7E-M
  uxtb_2 = "fa5ff080DM",
  uxtb_3 = "fa5ff080DMv",
  uxtb16_2 = "fa3ff080DM",   -- v7E-M
  uxtb16_3 = "fa3ff080DMv",  -- v7E-M
  uxth_2 = "fa1ff080DM",
  uxth_3 = "fa1ff080DMv",


  -- VFP instructions.
  ["vadd.f32_3"] = "ee300a00dnm",
  ["vadd.f64_3"] = "ee300b00Gdnm",
  ["vsub.f32_3"] = "ee300a40dnm",
  ["vsub.f64_3"] = "ee300b40Gdnm",
  ["vmul.f32_3"] = "ee200a00dnm",
  ["vmul.f64_3"] = "ee200b00Gdnm",
  ["vnmul.f32_3"] = "ee200a40dnm",
  ["vnmul.f64_3"] = "ee200b40Gdnm",
  ["vmla.f32_3"] = "ee000a00dnm",
  ["vmla.f64_3"] = "ee000b00Gdnm",
  ["vmls.f32_3"] = "ee000a40dnm",
  ["vmls.f64_3"] = "ee000b40Gdnm",
  ["vnmla.f32_3"] = "ee100a40dnm",
  ["vnmla.f64_3"] = "ee100b40Gdnm",
  ["vnmls.f32_3"] = "ee100a00dnm",
  ["vnmls.f64_3"] = "ee100b00Gdnm",
  ["vdiv.f32_3"] = "ee800a00dnm",
  ["vdiv.f64_3"] = "ee800b00Gdnm",

  ["vabs.f32_2"] = "eeb00ac0dm",
  ["vabs.f64_2"] = "eeb00bc0Gdm",
  ["vneg.f32_2"] = "eeb10a40dm",
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
  vmov_2 = "ee100a10Tn|ee000a10nT",
  vmov_3 = "ec500a10TNm|ec400a10mTN|ec500b10GTNm|ec400b10GmTN",

  vmrs_0 = "eef1fa10",
  vmrs_1 = "eef10a10T",
  vmsr_1 = "eee10a10T",

  ["vcvt.s32.f32_2"] = "eebd0ac0dm",
  ["vcvt.s32.f64_2"] = "eebd0bc0dGm",
  ["vcvt.u32.f32_2"] = "eebc0ac0dm",
  ["vcvt.u32.f64_2"] = "eebc0bc0dGm",
  ["vcvtr.s32.f32_2"] = "eebd0a40dm",
  ["vcvtr.s32.f64_2"] = "eebd0b40dGm",
  ["vcvtr.u32.f32_2"] = "eebc0a40dm",
  ["vcvtr.u32.f64_2"] = "eebc0b40dGm",
  ["vcvt.f32.s32_2"] = "eeb80ac0dm",
  ["vcvt.f64.s32_2"] = "eeb80bc0GdFm",
  ["vcvt.f32.u32_2"] = "eeb80a40dm",
  ["vcvt.f64.u32_2"] = "eeb80b40GdFm",
  ["vcvt.f32.f64_2"] = "eeb70bc0dGm",
  ["vcvt.f64.f32_2"] = "eeb70ac0GdFm",

  -- VFPv4 only:
  ["vfma.f32_3"] = "eea00a00dnm",
  ["vfma.f64_3"] = "eea00b00Gdnm",
  ["vfms.f32_3"] = "eea00a40dnm",
  ["vfms.f64_3"] = "eea00b40Gdnm",
  ["vfnma.f32_3"] = "ee900a40dnm",
  ["vfnma.f64_3"] = "ee900b40Gdnm",
  ["vfnms.f32_3"] = "ee900a00dnm",
  ["vfnms.f64_3"] = "ee900b00Gdnm",

  -- NYI: I have no need for these instructions right now:
  -- swp, swpb, strex, ldrex, strexd, ldrexd, strexb, ldrexb, strexh, ldrexh
  -- msr, nopv6, yield, wfe, wfi, sev, dbg, bxj, smc, srs, rfe
  -- cps, setend, pli, pld, pldw, clrex, dsb, dmb, isb
  -- stc, ldc, mcr, mcr2, mrc, mrc2, mcrr, mcrr2, mrrc, mrrc2, cdp, cdp2
}

-- Add mnemonics for "s" variants.
do
  local t = {}
  for k,v in pairs(map_op) do
    local vout = ""
    for vx in gmatch(v, "([^|]+)") do
      if sub(vx, -1) == "s" then
        vout = vout.."|"..sub(vx, 1, 2)..char(byte(vx, 3)+1)..sub(vx, 4, -2)
      end
    end
    if match(vout, "(.)") then
      t[sub(k, 1, -3).."s"..sub(k, -2)] = sub(vout, 1)
    end
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
      return 0
    end
  end
  werror("bad register name `"..expr.."'")
end

local function parse_vr(expr, tp, rp, hp)
  local t, r = match(expr, "^([sd])([0-9]+)$")
  if t == tp then
    r = tonumber(r)
    if r <= 31 then
      if t == "s" then return shl(shr(r, 1), rp) + shl(band(r, 1), hp) end
      return shl(band(r, 15), rp) + shl(shr(r, 4), hp)
    end
  end
  local tv, rv = match(expr, "^([sd])%(([^)]+)%)$")
  if tv == tp then
    -- store as action to read later
    if tv == "s" then
      wimmaction(rv, 1, 4, rp, false)
      wimmaction(rv, 0, 1, hp, false)
    else
      wimmaction(rv, 0, 4, rp, false)
      wimmaction(rv, 4, 1, hp, false)
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
  imm = match(imm, "^#(.*)$")
  if not imm then werror("expected immediate operand") end
  local n = tonumber(imm)
  if n then
    if n <= 255 then
      return band(n, 255)
    elseif band(n, 0xFF00FF00) == 0 and band(bxor(shr(n, 16), n), 0x00FF) == 0 then
      return bor(band(n, 255), shl(1, 12))
    elseif band(n, 0x00FF00FF) == 0 and band(bxor(shr(n, 16), n), 0xFF00) == 0 then
      return bor(band(shr(n, 8), 0xFF), shl(2, 12))
    elseif band(bxor(band(shr(n, 16), 0xFFFF), n), 0xFFFF) == 0 and band(bxor(band(shr(n, 8), 0xFF), n), 0xFF) == 0 then
      return bor(band(shr(n, 8), 0xFF), shl(3, 12))
    else
      local intbytes = 4
      for i=0,32,1 do
        if n >= 0x80 and n <= 0xFF then
          local result = band(n, 0x7F)
          result = bor(result, shl(band(i, 0x01), 7))
          result = bor(result, shl(band(i, 0x0E), 12-1))
          result = bor(result, shl(band(i, 0x10), 26-4))
          return result
        end
        n = bor(shl(n, 1), shr(n, 31)) -- assumes 32-bit int
      end
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
    result =          parse_imm_n(n, 8, 0, 0, false, true)
    result = result + parse_imm_n(n, 3, 12, 8, true, true)
    result = result + parse_imm_n(n, 1, 26, 11, true, true)
    result = result + parse_imm_n(n, 4, 16, 12, true, false)
    return result
  else
    waction("IMM16", 32*16, imm)
    return 0
  end
end

local function parse_imm_load(imm)
  local n = tonumber(imm)
  if n then
    if n < 0 then
      -- IMM2, 8-bit immediate with sign
      if n >= -255 and n <= 255 then
        local up = 0x200  -- bit 9
        if n < 0 then n = -n; up = 0 end
        return n + up + 0x800
      end
    else
      if n <= 4095 then
        -- IMM1, 12-bit immediate without sign
        return n + 0x00800000  -- set U bit
      end
    end
    werror("out of range immediate `"..imm.."'")
  else
    waction("IMML", 32768 + shl(12, 5), imm)
    return 0
  end
end

local function parse_shift(shift)
  if shift == "rrx" then
    return shl(3, 4)
  else
    local s, s2 = match(shift, "^(%S+)%s*(.*)$")
    s = map_shift[s]
    if not s then werror("expected shift operand") end
    if sub(s2, 1, 1) == "#" then
      -- shift in bit 4, then the bottom 2 bits of imm starting bit 6, then the other 3 bits starting bit 12
      return shl(s, 4) + parse_imm(s2, 2, 6, 0, false, true) + parse_imm(s2, 3, 12, 2, true)
    else
      werror("expected immediate shift operand")
    end
  end
end

local function parse_rorshift(s, scale, bits, shift)
  local op, s2 = match(s, "^(%S+)%s*(.*)$")
  if op ~= "ror" then werror("only valid rotation here is ror") end
  if sub(s2, 1, 1) == "#" then
    local n = tonumber(sub(s2, 2))
    if n then
      return parse_imm_n(n, bits, shift, scale, false, false)
    else
      werror("expected numeric immediate operand")
    end
  else
    werror("expected immediate shift operand")
  end
end

local function parse_satshift(s)
  local op, s2 = match(s, "^(%S+)%s*(.*)$")
  if op ~= "lsl" and op ~= "asr" then werror("only valid rotations here are lsl and asr") end
  if sub(s2, 1, 1) == "#" then
    local n = tonumber(sub(s2, 2))
    s = map_shift[s]
    if n then
      if n <= 31 and (op == "lsl" and n >= 0) or (op == "asr" and n > 0) then
        return shl(s, 20) + parse_imm_n(n, 2, 6, 0, false, true) + parse_imm_n(n, 3, 12, 2, true, false)
      else
        werror("expected numeric immediate operand between 0 (LSL) or 1 (ASR) and 31")
      end
    else
      werror("expected numeric immediate operand")
    end
  else
    werror("expected immediate shift operand")
  end
end

local function parse_label(label, def, pbase)
  local prefix = sub(label, 1, 2)
  local base = pbase and pbase or 0
  -- =>label (pc label reference)
  if prefix == "=>" then
    return "PC", base, sub(label, 3)
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
  local ophi = shr(op, 20)
  local pn = params[n]
  local p1, wb = match(pn, "^%[%s*(.-)%s*%](!?)$")
  local p2 = params[n+1]
  if not p1 then
    if not p2 then
      -- label?
      if match(pn, "^[<>=%-]") or match(pn, "^extern%s+") or match(pn, "^ptr%s+") then
        local mode, n, s = parse_label(pn, false)
        waction("REL_"..mode, n, s, 1)
        -- LIT: op + (1111 -> Rn)
        return op + 15 * 65536
      end
      -- GPR?
      local reg, tailr = match(pn, "^([%w_:]+)%s*(.*)$")
      if reg and tailr ~= "" then
        local d, tp = parse_gpr(reg, 16)
        if tp then
          waction("IMML", 32768 + 32*12, format(tp.ctypefmt, tailr))
          -- IMM1/2: op + (d -> Rn)
          return op + d
        end
      end
    end
    werror("expected address operand")
  end
  if wb == "!" then op = op + 0x00000100 end  -- only supported by IMM2
  if p2 then
    -- IMM1/2
    if wb == "!" then werror("bad use of '!'") end
    local p3 = params[n+2]
    op = op + parse_gpr(p1, 16)  -- p1 -> Rn
    local imm = match(p2, "^#(.*)$")
    if imm then
      local m = parse_imm_load(imm)
      if p3 then werror("too many parameters") end
      op = op + m
    end
    werror("expected immediate as final argument to LDR/STR")
  else
    local p1a, p2 = match(p1, "^([^,%s]*)%s*(.*)$")
    op = op + parse_gpr(p1a, 16)
    if p2 ~= "" then
      local imm = match(p2, "^,%s*#(.*)$")
      if imm then
        -- IMM1/2
        local m = parse_imm_load(imm)
        op = op + m
      else
        -- REG
        local p2a, p3 = match(p2, "^,%s*([^,%s]*)%s*,?%s*(.*)$")
        op = op + parse_gpr(p2a, 0)
        if p3 ~= "" then
          local p3s = parse_shift(p3)
          if band(p3s, 0x3F) ~= 0 or band(p3s, 0x7000) ~= 0 then
            werror("only valid shift operand to LDR/STR is LSL #0-3")
          end
          op = op + shr(p3s, 2)  -- shift[0-1] normally in bits 6+, we want them in 4+
        end
      end
    else
      if wb == "!" then werror("bad use of '!'") end
      op = op + 0x00800000
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
      waction("REL_"..mode, n + 16384, s, 1)
      return 15 * 65536  -- encode PC as Rn
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

local function parse_lsbwidth(params, nparams, n, op)
  -- The required value of msbit is <lsb>+<width>-1
  if n + 1 <= nparams then
    lsb = tonumber(params[n+0])
    width = tonumber(params[n+1])
    if lsb and width then
      msbit = lsb + width - 1
      op = op + parse_imm_n(lsb, 2, 6, 0, false, true)
      op = op + parse_imm_n(lsb, 3, 12, 2, true, false)
      op = op + parse_imm_n(msbit, 5, 0, 0, false, false)
      return op
    else
      -- TODO: write action?
    end
  end
  werror("expected two immediate arguments for lsb/width")
end

------------------------------------------------------------------------------

-- Handle opcodes defined with template strings.
local function parse_template(params, template, nparams, pos)
  local op = tonumber(sub(template, 1, 8), 16)
  local n = 1
  local vr = "s"
  local lastx = nil
  local nparams = nparams or #params

  -- Process each character.
  for p in gmatch(sub(template, 9), ".") do
    local q = params[n]
    if p == "D" then
      op = op + parse_gpr(q, 8);  n = n + 1
    elseif p == "T" then
      op = op + parse_gpr(q, 12); n = n + 1
    elseif p == "N" then
      op = op + parse_gpr(q, 16); n = n + 1
    elseif p == "M" then
      op = op + parse_gpr(q, 0);  n = n + 1
    elseif p == "Z" then  -- M, and M in the N slot
      op = op + parse_gpr(q, 0) + parse_gpr(q, 16); n = n + 1
    elseif p == "j" then
      op = op + parse_gpr(q, thumb_rm); n = n + 1
    elseif p == "d" then
      op = op + parse_vr(q, vr, 12, 22); n = n + 1
    elseif p == "n" then
      op = op + parse_vr(q, vr, 16, 7); n = n + 1
    elseif p == "m" then
      op = op + parse_vr(q, vr, 0, 5); n = n + 1
    elseif p == "p" then
      op = op + parse_shift(q, true); n = n + 1
    elseif p == "v" then
      op = op + parse_rorshift(q, 3, 2, 4); n = n + 1
    elseif p == "L" then
      op = parse_load(params, nparams, n, op)
    elseif p == "l" then
      op = op + parse_vload(q); n = n + 1
    elseif p == "z" then
      op = parse_lsbwidth(params, nparams, n, op)
      n = n + 2
    elseif p == "x" then
      op = op + parse_imm(q, 2, 6, 0, false, true)
      op = op + parse_imm(q, 3, 12, 2, true, false)
      n = n + 1
    elseif p == "w" then
      -- bit 23 is set for ssat*, not for usat*
      local offset = (band(op, shl(1, 23)) == 0) and -1 or 0
      op = op + parse_immo(q, offset, 5, 0, 0); n = n + 1
    elseif p == "y" then
      op = op + parse_satshift(q); n = n + 1
    elseif p == "B" then
      local mode, n, s = parse_label(q, false, 32768 + 16384)
      waction("REL_"..mode, n, s, 1); n = n + 1
    elseif p == "b" then
      local mode, n, s = parse_label(q, false, 32768)
      waction("REL_"..mode, n, s, 1); n = n + 1
    elseif p == "J" then
      local mode, n, s = parse_label(q, false, 8192)  -- ADR-style
      waction("REL_"..mode, n, s, 1); n = n + 1
    elseif p == "F" then
      vr = "s"
    elseif p == "G" then
      vr = "d"
    elseif p == "o" then  -- N with possible writeback
      local r, wb = match(q, "^([^!]*)(!?)$")
      op = op + parse_gpr(r, 16) + (wb == "!" and 0x00200000 or 0)
      n = n + 1
    elseif p == "R" then
      op = op + parse_reglist(q); n = n + 1
    elseif p == "r" then
      op = op + parse_vrlist(q); n = n + 1
    elseif p == "W" then
      op = op + parse_imm16(q); n = n + 1
    elseif p == "I" then
      op = op + parse_imm12(q); n = n + 1
    elseif p == "i" then
      op = op + parse_imm(q, 8, 0, 0, false, true)
      op = op + parse_imm(q, 3, 12, 8, true, true)
      op = op + parse_imm(q, 1, 26, 11, true, false)
      n = n + 1
    elseif p == "K" then
      op = op + parse_imm(q, 0, 8, 16); n = n + 1
    elseif p == "Y" then  -- used by VFP
      local imm = tonumber(match(q, "^#(.*)$")); n = n + 1
      if not imm or shr(imm, 8) ~= 0 then
        werror("bad immediate operand")
      end
      op = op + shl(band(imm, 0xf0), 12) + band(imm, 0x0f)
    elseif p == "s" then
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

function writelong(p, flip)
  local n = tonumber(p)
  if n then
    if flip then
      n = bor(shr(n, 16), shl(band(n, 0xFFFF), 16))
    end
    if n < 0 then n = n + 2^32 end
    wputraw(n)
  else
    local pstr = ""
    if flip then
      pstr = "(((uint32_t)("..p..") >> 16) | (((uint32_t)("..p..") & 0xFFFF) << 16))"
    else
      pstr = "(uint32_t)("..p..")"
    end
    wputraw(0)
    waction("IMM32", 0, pstr)
  end
  if secpos+2 > maxsecpos then wflush() end
end

-- Pseudo-opcode for data storage.
-- Pre-flip data so it is flipped back before being emitted
map_op[".long_*"] = function(params)
  if not params then return "imm..." end
  for _,p in ipairs(params) do
    writelong(p, true)
  end
end

-- Pseudo-opcode for instruction storage.
map_op[".ilong_*"] = function(params)
  if not params then return "imm..." end
  for _,p in ipairs(params) do
    writelong(p, false)
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
    -- TODO: handle conditionals appropriately for Thumb-2 (this is wrong)
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

