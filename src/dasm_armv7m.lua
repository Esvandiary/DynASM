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
local band, shl, shr, sar = bit.band, bit.lshift, bit.rshift, bit.arshift
local ror, tohex = bit.ror, bit.tohex

-- Inherited tables and callbacks.
local g_opt, g_arch
local wline, werror, wfatal, wwarn

-- Action name list.
-- CHECK: Keep this in sync with the C code!
local action_names = {
  "STOP", "SECTION", "ESC", "REL_EXT",
  "ALIGN", "REL_LG", "LABEL_LG",
  "REL_PC", "LABEL_PC", "IMM", "IMM12", "IMM16", "IMML8", "IMML12", "IMMV8",
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
  if n <= 0x000fffff then waction("ESC") end
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
  if n <= 0x000fffff then
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
  adc_3 = "f1400000DNIs|eb400000DNMs",
  adc_4 = "eb400000DNMps",
  add_3 = "f1000000DNIs|eb000000DNMs",
  add_4 = "eb000000DNMps",
  addw_3 = "f2000000DNI",
  adr_2 = "f20f0000DJ", -- bits 21/23 different depending on direction: before = 1, after = 0
  and_3 = "f0000000DNIs|ea000000DNMs",
  and_4 = "ea000000DNMps",
  asr_3 = "ea4f0020DMxs|fa40f000DNMs",
  b_1 = "f0009000W",
  bal_1 = "f0009000W",
  beq_1 = "f0008000V",
  bne_1 = "f0408000V",
  bcs_1 = "f0808000V",
  bcc_1 = "f0c08000V",
  bmi_1 = "f1008000V",
  bpl_1 = "f1408000V",
  bvs_1 = "f1808000V",
  bvc_1 = "f1c08000V",
  bhi_1 = "f2008000V",
  bls_1 = "f2408000V",
  bge_1 = "f2808000V",
  blt_1 = "f2c08000V",
  bgt_1 = "f3008000V",
  ble_1 = "f3408000V",
  bl_1 = "f000d000W",
  blal_1 = "f000d000W",
  blx_1 = "4780bf00w",   -- with bonus nop
  bx_1 = "4700bf00w",    -- with bonus nop
  bfc_3 = "f36f0000Dxz",
  bfi_4 = "f3600000DNxz",
  bic_3 = "f0200000DNIs|ea200000DNMs",
  bic_4 = "ea200000DNMps",
  bkpt_1 = "be00bf00K",  -- with bonus nop
  cbz_2 = "b100bf00kC",  -- with bonus nop
  cbnz_2 = "b900bf00kC", -- with bonus nop
  clz_2 = "fab0f080DZ",
  cmn_2 = "f1100f00NI|eb100f00NM", -- condition flags only -- condition flags only
  cmn_3 = "eb100f00NMp",-- condition flags only
  cmp_2 = "f1b00f00NI|ebb00f00NM", -- condition flags only -- condition flags only
  cmp_3 = "ebb00f00NMp",-- condition flags only
  eor_3 = "f0800000DNIs|ea800000DNMs",
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
  ldrd_2 = "e8500000DT",
  ldrd_3 = "e8500000DTL",
  ldrd_4 = "e8500000DTL",
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
  lsl_3 = "ea4f0000DMxs|fa0ff000DNMs",
  lsr_3 = "ea4f0010DMxs|fa2ff000DNMs",
  mla_4 = "fb000000DNMT",
  mls_4 = "fb000010DNMT",
  mov_2 = "f04f0000DIs|ea4f0000DMs",
  movw_2 = "f2400000Dy",
  movt_2 = "f2c00000Dy",
  mul_3 = "fb00f000DNM",
  mvn_2 = "f06f0000DIs|ea6f0000DMps",
  neg_2 = "f1d00000DN",   -- alias for RSBS Rd, Rn, #0
  nop_0 = "bf00bf00|f3af8000",
  orn_3 = "f0600000DNIs|ea600000DNMs",
  orn_4 = "ea600000DNMps",
  orr_3 = "f0400000DNIs|ea400000DNMs",
  orr_4 = "ea400000DNMps",
  pkhbt_3 = "eac00000DNM",  -- v7E-M
  pkhbt_4 = "eac00000DNMx", -- v7E-M
  pkhtb_3 = "eac00020DNM",  -- v7E-M
  pkhtb_4 = "eac00020DNMx", -- v7E-M
  pop_1 = "e8bd0000R|f85d0b04T",
  push_1 = "e92d0000R|f84d0d00T",
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
  ror_3 = "ea4f0030DMxs|fa60f000DNMs",
  rrx_2 = "ea4f0030DMs",
  rsb_3 = "f1c00000DNIs|ebc00000DNMs",
  rsb_4 = "ebc00000DNMps",
  sadd16_3 = "fa90f000DNM", -- v7E-M
  sadd8_3 = "fa80f000DNM",  -- v7E-M
  sasx_3 = "faa0f000DNM",   -- v7E-M
  sbc_3 = "f1600000DNIs|eb600000DNMs",
  sbc_4 = "eb600000DNMps",
  sbfx_4 = "f3400000DNxz",
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
  ssat_3 = "f3000000DzN",     -- bit 21 is "sh", unhandled
  ssat_4 = "f3000000DzNx",    -- bit 21 is "sh", unhandled
  ssat16_3 = "f3200000DzN",   -- imm is 4 bits not 5 :(
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
  strd_4 = "e8400000TDL",
  strh_2 = "f8200000TL",
  strh_3 = "f8200000TL",
  strht_2 = "f8200e00TL",
  strht_3 = "f8200e00TL",
  strt_3 = "f8400e00TL",
  sub_3 = "f1a00000DNIs|eba00000DNMs",
  sub_4 = "eba00000DNMps",
  subw_3 = "f2a00000DNI",
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
  teq_2 = "f0900f00NI|ea900f00NM",  -- condition flags only  -- condition flags only
  teq_3 = "ea900f00NMI", -- condition flags only
  tst_2 = "f0100f00NI|ea100f00NM",  -- condition flags only  -- condition flags only
  tst_3 = "ea100f00NMI", -- condition flags only
  uadd16_3 = "fa90f040DNM", -- v7E-M
  uadd8_3 = "fa80f040DNM",  -- v7E-M
  uasx_3 = "faa0f040DNM",   -- v7E-M
  ubfx_4 = "f3c00000DNxz",
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
  usat_3 = "f3800000DzN",   -- bit 21 is "sh", unhandled
  usat_4 = "f3800000DzNx",  -- bit 21 is "sh", unhandled
  usat16_3 = "f3a00000DzN", -- v7E-M, imm is actually 4 bits :(
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
  vmov_2 = "ee100a10Dn|ee000a10nD",
  vmov_3 = "ec500a10DNm|ec400a10mDN|ec500b10GDNm|ec400b10GmDN",

  vmrs_0 = "eef1fa10",
  vmrs_1 = "eef10a10D",
  vmsr_1 = "eee10a10D",

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

  -- NYI: Advanced SIMD instructions.

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
    if sub(v, -1) == "s" then
      local v2 = sub(v, 1, 2)..char(byte(v, 3)+1)..sub(v, 4, -2)
      -- TODO: fix this logic for .w names
      t[sub(k, 1, -3).."s"..sub(k, -2)] = v2
    end
  end
  for k,v in pairs(t) do
    map_op[k] = v
  end
end

------------------------------------------------------------------------------

local function parse_gpr(expr)
  local tname, ovreg = match(expr, "^([%w_]+):(r1?[0-9])$")
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
    if r <= 15 then return r, tp end
  end
  werror("bad register name `"..expr.."'")
end

local function parse_gpr_pm(expr)
  local pm, expr2 = match(expr, "^([+-]?)(.*)$")
  return parse_gpr(expr2), (pm == "-")
end

local function parse_vr(expr, tp)
  local t, r = match(expr, "^([sd])([0-9]+)$")
  if t == tp then
    r = tonumber(r)
    if r <= 31 then
      if t == "s" then return shr(r, 1), band(r, 1) end
      return band(r, 15), shr(r, 4)
    end
  end
  werror("bad register name `"..expr.."'")
end

-- TODO: handle stupid difference between 1 reg set and >1 in POP/PUSH
-- normally reglist is [15:0], if only 1 set then it lives in [15:12] (Rt)
local function parse_reglist(reglist)
  reglist = match(reglist, "^{%s*([^}]*)}$")
  if not reglist then werror("register list expected") end
  local rr = 0
  for p in gmatch(reglist..",", "%s*([^,]*),") do
    local rbit = shl(1, parse_gpr(gsub(p, "%s+$", "")))
    if band(rr, rbit) ~= 0 then
      werror("duplicate register `"..p.."'")
    end
    rr = rr + rbit
  end
  return rr
end

local function parse_vrlist(reglist)
  local ta, ra, tb, rb = match(reglist,
                           "^{%s*([sd])([0-9]+)%s*%-%s*([sd])([0-9]+)%s*}$")
  ra, rb = tonumber(ra), tonumber(rb)
  if ta and ta == tb and ra and rb and ra <= 31 and rb <= 31 and ra <= rb then
    local nr = rb+1 - ra
    if ta == "s" then
      return shl(shr(ra,1),12)+shl(band(ra,1),22) + nr
    else
      return shl(band(ra,15),12)+shl(shr(ra,4),22) + nr*2 + 0x100
    end
  end
  werror("register list expected")
end

local function parse_imm(imm, bits, shift, scale, signed, allowlossy)
  imm = match(imm, "^#(.*)$")
  if not imm then werror("expected immediate operand") end
  local n = tonumber(imm)
  if n then
    local m = sar(n, scale)
    if allowlossy or shl(m, scale) == n then
      if signed then
        local s = sar(m, bits-1)
        if s == 0 then return shl(m, shift)
        elseif s == -1 then return shl(m + shl(1, bits), shift) end
      else
        if sar(m, bits) == 0 then return shl(m, shift) end
      end
    end
    werror("out of range immediate `"..imm.."'")
  else
    waction("IMM", (signed and 32768 or 0)+scale*1024+bits*32+shift, imm)
    return 0
  end
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

local function parse_shift(shift)
  if shift == "rrx" then
    return 3 * 32
  else
    local s, s2 = match(shift, "^(%S+)%s*(.*)$")
    s = map_shift[s]
    if not s then werror("expected shift operand") end
    if sub(s2, 1, 1) == "#" then
      -- shift in bit 4, then the bottom 2 bits of imm starting bit 6, then the other 3 bits starting bit 12
      return shl(s, 4) + parse_imm(s2, 2, 6, 0, false, true) + parse_imm(s2, 3, 12, 2, false, true)
    else
      werror("expected immediate shift operand")
    end
  end
end

local function parse_label(label, def)
  local prefix = sub(label, 1, 2)
  -- =>label (pc label reference)
  if prefix == "=>" then
    return "PC", 0, sub(label, 3)
  end
  -- ->name (global label reference)
  if prefix == "->" then
    return "LG", map_global[sub(label, 3)]
  end
  if def then
    -- [1-9] (local label definition)
    if match(label, "^[1-9]$") then
      return "LG", 10+tonumber(label)
    end
  else
    -- [<>][1-9] (local label reference)
    local dir, lnum = match(label, "^([<>])([1-9])$")
    if dir then -- Fwd: 1-9, Bkwd: 11-19.
      return "LG", lnum + (dir == ">" and 0 or 10)
    end
    -- extern label (extern label reference)
    local extname = match(label, "^extern%s+(%S+)$")
    if extname then
      return "EXT", map_extern[extname]
    end
  end
  werror("bad label `"..label.."'")
end

-- TOCHECK
local function parse_load(params, nparams, n, op)
  local oplo = band(op, 255)
  local ext, ldrd = (oplo ~= 0), (oplo == 208) -- TODO: correct ldrd opcode
  local d
  if (ldrd or oplo == 240) then -- TOCHECK: 240
    d = band(shr(op, 12), 15)
    if band(d, 1) ~= 0 then werror("odd destination register") end
  end
  local pn = params[n]
  local p1, wb = match(pn, "^%[%s*(.-)%s*%](!?)$")
  local p2 = params[n+1]
  if not p1 then
    if not p2 then
      if match(pn, "^[<>=%-]") or match(pn, "^extern%s+") then
        local mode, n, s = parse_label(pn, false)
        waction("REL_"..mode, n + (ext and 0x1800 or 0x0800), s, 1)
        return op + 15 * 65536 + 0x01000000 + (ext and 0x00400000 or 0)
      end
      local reg, tailr = match(pn, "^([%w_:]+)%s*(.*)$")
      if reg and tailr ~= "" then
        local d, tp = parse_gpr(reg)
        if tp then
          waction(ext and "IMML8" or "IMML12", 32768 + 32*(ext and 8 or 12),
                  format(tp.ctypefmt, tailr))
          return op + shl(d, 16) + 0x01000000 + (ext and 0x00400000 or 0)
        end
      end
    end
    werror("expected address operand")
  end
  if wb == "!" then op = op + 0x00200000 end -- correct for Thumb-2
  if p2 then
    if wb == "!" then werror("bad use of '!'") end
    local p3 = params[n+2]
    op = op + shl(parse_gpr(p1), 16)
    local imm = match(p2, "^#(.*)$")
    if imm then
      local m = parse_imm_load(imm, ext)
      if p3 then werror("too many parameters") end
      op = op + m + (ext and 0x00400000 or 0)
    else
      local m, neg = parse_gpr_pm(p2)
      if ldrd and (m == d or m-1 == d) then werror("register conflict") end
      op = op + m + (neg and 0 or 0x00800000) + (ext and 0 or 0x02000000)
      if p3 then op = op + parse_shift(p3) end
    end
  else
    local p1a, p2 = match(p1, "^([^,%s]*)%s*(.*)$")
    op = op + shl(parse_gpr(p1a), 16) + 0x01000000
    if p2 ~= "" then
      local imm = match(p2, "^,%s*#(.*)$")
      if imm then
        local m = parse_imm_load(imm, ext)
        op = op + m + (ext and 0x00400000 or 0)
      else
        local p2a, p3 = match(p2, "^,%s*([^,%s]*)%s*,?%s*(.*)$")
        local m, neg = parse_gpr_pm(p2a)
        if ldrd and (m == d or m-1 == d) then werror("register conflict") end
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
    local d = shl(parse_gpr(reg), 16)
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
      local d, tp = parse_gpr(reg)
      if tp then
        waction("IMMV8", 32768 + 32*8, format(tp.ctypefmt, tailr))
        return shl(d, 16)
      end
    end
  end
  werror("expected address operand")
end

------------------------------------------------------------------------------

-- Handle opcodes defined with template strings.
local function parse_template(params, template, nparams, pos)
  local op = tonumber(sub(template, 1, 8), 16)
  local n = 1
  local vr = "s"

  -- Process each character.
  for p in gmatch(sub(template, 9), ".") do
    local q = params[n]
    if p == "D" then
      op = op + shl(parse_gpr(q), 8); n = n + 1
    elseif p == "T" then
      op = op + shl(parse_gpr(q), 12); n = n + 1
    elseif p == "N" then
      op = op + shl(parse_gpr(q), 16); n = n + 1
    elseif p == "M" then
      op = op + parse_gpr(q); n = n + 1
    elseif p == "Z" then  -- M, and M in the N slot
      local mgpr = parse_gpr(q); op = op + mgpr + shl(mgpr, 16); n = n + 1
    elseif p == "d" then
      local r,h = parse_vr(q, vr); op = op+shl(r,12)+shl(h,22); n = n + 1
    elseif p == "n" then
      local r,h = parse_vr(q, vr); op = op+shl(r,16)+shl(h,7); n = n + 1
    elseif p == "m" then
      local r,h = parse_vr(q, vr); op = op+r+shl(h,5); n = n + 1
    elseif p == "p" then
      op = op + parse_shift(q, true); n = n + 1
    elseif p == "L" then
      op = parse_load(params, nparams, n, op)
    elseif p == "l" then
      op = op + parse_vload(q)
    elseif p == "B" then
      local mode, n, s = parse_label(q, false)
      waction("REL_"..mode, n, s, 1)
    elseif p == "F" then
      vr = "s"
    elseif p == "G" then
      vr = "d"
    elseif p == "o" then  -- N with possible writeback
      local r, wb = match(q, "^([^!]*)(!?)$")
      op = op + shl(parse_gpr(r), 16) + (wb == "!" and 0x00200000 or 0)
      n = n + 1
    elseif p == "R" then
      op = op + parse_reglist(q); n = n + 1
    elseif p == "r" then
      op = op + parse_vrlist(q); n = n + 1
    elseif p == "W" then
      op = op + parse_imm16(q); n = n + 1
    elseif p == "v" then
      op = op + parse_imm(q, 5, 7, 0, false); n = n + 1
    elseif p == "w" then
      local imm = match(q, "^#(.*)$")
      if imm then
        op = op + parse_imm(q, 5, 7, 0, false); n = n + 1
      else
        op = op + shl(parse_gpr(q), 8) + 16
      end
    elseif p == "X" then
      op = op + parse_imm(q, 5, 16, 0, false); n = n + 1
    elseif p == "Y" then  -- used by VFP
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
      op = op + parse_imm(q, 24, 0, 0, false); n = n + 1
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

-- Pseudo-opcodes for data storage.
map_op[".long_*"] = function(params)
  if not params then return "imm..." end
  for _,p in ipairs(params) do
    local n = tonumber(p)
    if not n then werror("bad immediate `"..p.."'") end
    if n < 0 then n = n + 2^32 end
    wputw(n)
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

