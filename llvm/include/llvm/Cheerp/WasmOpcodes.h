//===-- Cheerp/WasmOpcodes.h - Cheerp utility code ---------------------===//
//
//                     Cheerp: The C++ compiler for the Web
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
// Copyright 2020 Leaning Technologies
//
//===----------------------------------------------------------------------===//

#ifndef _CHEERP_WASM_OPCODES_H
#define _CHEERP_WASM_OPCODES_H

enum class WasmOpcode {
	UNREACHABLE = 0x00,
	ELSE = 0x05,
	END = 0x0b,
	BR_TABLE = 0x0e,
	RETURN = 0x0f,
	DROP = 0x1a,
	SELECT = 0x1b,
	F32_CONST = 0x43,
	I32_EQZ = 0x45,
	I32_EQ = 0x46,
	I32_NE = 0x47,
	I32_LT_S = 0x48,
	I32_LT_U = 0x49,
	I32_GT_S = 0x4a,
	I32_GT_U = 0x4b,
	I32_LE_S = 0x4c,
	I32_LE_U = 0x4d,
	I32_GE_S = 0x4e,
	I32_GE_U = 0x4f,
	I64_EQ = 0x51,
	I64_EQZ = 0x50,
	I64_NE = 0x52,
	I64_LT_S = 0x53,
	I64_LT_U = 0x54,
	I64_GT_S = 0x55,
	I64_GT_U = 0x56,
	I64_LE_S = 0x57,
	I64_LE_U = 0x58,
	I64_GE_S = 0x59,
	I64_GE_U = 0x5a,
	F32_EQ = 0x5b,
	F32_NE = 0x5c,
	F32_LT = 0x5d,
	F32_GT = 0x5e,
	F32_LE = 0x5f,
	F32_GE = 0x60,
	F64_EQ = 0x61,
	F64_NE = 0x62,
	F64_LT = 0x63,
	F64_GT = 0x64,
	F64_LE = 0x65,
	F64_GE = 0x66,
	I32_CLZ = 0x67,
	I32_CTZ = 0x68,
	I32_POPCNT = 0x69,
	I32_ADD = 0x6a,
	I32_SUB = 0x6b,
	I32_MUL = 0x6c,
	I32_DIV_S = 0x6d,
	I32_DIV_U = 0x6e,
	I32_REM_S = 0x6f,
	I32_REM_U = 0x70,
	I32_AND = 0x71,
	I32_OR = 0x72,
	I32_XOR = 0x73,
	I32_SHL = 0x74,
	I32_SHR_S = 0x75,
	I32_SHR_U = 0x76,
	I64_CLZ = 0x79,
	I64_CTZ = 0x7a,
	I64_POPCNT = 0x7b,
	I64_ADD = 0x7c,
	I64_SUB = 0x7d,
	I64_MUL = 0x7e,
	I64_DIV_S = 0x7f,
	I64_DIV_U = 0x80,
	I64_REM_S = 0x81,
	I64_REM_U = 0x82,
	I64_AND = 0x83,
	I64_OR = 0x84,
	I64_XOR = 0x85,
	I64_SHL = 0x86,
	I64_SHR_S = 0x87,
	I64_SHR_U = 0x88,
	F32_ABS = 0x8b,
	F32_NEG = 0x8c,
	F32_CEIL = 0x8d,
	F32_FLOOR = 0x8e,
	F32_TRUNC = 0x8f,
	F32_NEAREST = 0x90,
	F32_SQRT = 0x91,
	F32_ADD = 0x92,
	F32_SUB = 0x93,
	F32_MUL = 0x94,
	F32_DIV = 0x95,
	F32_MIN = 0x96,
	F32_MAX = 0x97,
	F32_COPYSIGN = 0x98,
	F64_ABS = 0x99,
	F64_NEG = 0x9a,
	F64_CEIL = 0x9b,
	F64_FLOOR = 0x9c,
	F64_TRUNC = 0x9d,
	F64_NEAREST = 0x9e,
	F64_SQRT = 0x9f,
	F64_ADD = 0xa0,
	F64_SUB = 0xa1,
	F64_MUL = 0xa2,
	F64_DIV = 0xa3,
	F64_MIN = 0xa4,
	F64_MAX = 0xa5,
	F64_COPYSIGN = 0xa6,
	I32_WRAP_I64 = 0xa7,
	I32_TRUNC_S_F32 = 0xa8,
	I32_TRUNC_U_F32 = 0xa9,
	I32_TRUNC_S_F64 = 0xaa,
	I32_TRUNC_U_F64 = 0xab,
	I64_EXTEND_S_I32 = 0xac,
	I64_EXTEND_I32_U = 0xad,
	I64_TRUNC_S_F32 = 0xae,
	I64_TRUNC_U_F32 = 0xaf,
	I64_TRUNC_S_F64 = 0xb0,
	I64_TRUNC_U_F64 = 0xb1,
	F32_CONVERT_S_I32 = 0xb2,
	F32_CONVERT_U_I32 = 0xb3,
	F32_CONVERT_S_I64 = 0xb4,
	F32_CONVERT_U_I64 = 0xb5,
	F32_DEMOTE_F64 = 0xb6,
	F64_CONVERT_S_I32 = 0xb7,
	F64_CONVERT_U_I32 = 0xb8,
	F64_CONVERT_S_I64 = 0xb9,
	F64_CONVERT_U_I64 = 0xba,
	F64_PROMOTE_F32 = 0xbb,
	I32_REINTERPRET_F32 = 0xbc,
	I64_REINTERPRET_F64 = 0xbd,
	F32_REINTERPRET_I32 = 0xbe,
	F64_REINTERPRET_I64 = 0xbf,
	SIMD = 0xfd,
};

enum class WasmS32Opcode {
	GROW_MEMORY = 0x40,
	I32_CONST = 0x41,
};

enum class WasmS64Opcode {
	I64_CONST = 0x42,
};

enum class WasmU32Opcode {
	BLOCK = 0x02,
	LOOP = 0x03,
	IF = 0x04,
	BR = 0x0c,
	BR_IF = 0x0d,
	CALL = 0x10,
	RETURN_CALL = 0x12,
	GET_LOCAL = 0x20,
	SET_LOCAL = 0x21,
	TEE_LOCAL = 0x22,
	GET_GLOBAL = 0x23,
	SET_GLOBAL = 0x24,
};

enum class WasmU32U32Opcode {
	CALL_INDIRECT = 0x11,
	RETURN_CALL_INDIRECT = 0x13,
	I32_LOAD = 0x28,
	I64_LOAD = 0x29,
	F32_LOAD = 0x2a,
	F64_LOAD = 0x2b,
	I32_LOAD8_S = 0x2c,
	I32_LOAD8_U = 0x2d,
	I32_LOAD16_S = 0x2e,
	I32_LOAD16_U = 0x2f,
	I32_STORE = 0x36,
	I64_STORE = 0x37,
	F32_STORE = 0x38,
	F64_STORE = 0x39,
	I32_STORE8 = 0x3a,
	I32_STORE16 = 0x3b,
};

enum class WasmSIMDOpcode {
	V128_CONST = 0x0c,
	I8x16_SHUFFLE = 0x0d,
	I8x16_SWIZZLE = 0x0e,
	I8x16_SPLAT = 0x0f,
	I16x8_SPLAT = 0x10,
	I32x4_SPLAT = 0x11,
	I64x2_SPLAT = 0x12,
	F32x4_SPLAT = 0x13,
	F64x2_SPLAT = 0x14,
	I8x16_EQ = 0x23,
	I8x16_NE = 0x24,
	I8x16_LT_S = 0x25,
	I8x16_LT_U = 0x26,
	I8x16_GT_S = 0x27,
	I8x16_GT_U = 0x28,
	I8x16_LE_S = 0x29,
	I8x16_LE_U = 0x2a,
	I8x16_GE_S = 0x2b,
	I8x16_GE_U = 0x2c,
	I16x8_EQ = 0x2d,
	I16x8_NE = 0x2e,
	I16x8_LT_S = 0x2f,
	I16x8_LT_U = 0x30,
	I16x8_GT_S = 0x31,
	I16x8_GT_U = 0x32,
	I16x8_LE_S = 0x33,
	I16x8_LE_U = 0x34,
	I16x8_GE_S = 0x35,
	I16x8_GE_U = 0x36,
	I32x4_EQ = 0x37,
	I32x4_NE = 0x38,
	I32x4_LT_S = 0x39,
	I32x4_LT_U = 0x3a,
	I32x4_GT_S = 0x3b,
	I32x4_GT_U = 0x3c,
	I32x4_LE_S = 0x3d,
	I32x4_LE_U = 0x3e,
	I32x4_GE_S = 0x3f,
	I32x4_GE_U = 0x40,
	F32x4_EQ = 0x41,
	F32x4_NE = 0x42,
	F32x4_LT = 0x43,
	F32x4_GT = 0x44,
	F32x4_LE = 0x45,
	F32x4_GE = 0x46,
	F64x2_EQ = 0x47,
	F64x2_NE = 0x48,
	F64x2_LT = 0x49,
	F64x2_GT = 0x4a,
	F64x2_LE = 0x4b,
	F64x2_GE = 0x4c,
	V128_NOT = 0x4d,
	V128_AND = 0x4e,
	V128_OR = 0x50,
	V128_XOR = 0x51,
	V128_BITSELECT = 0x52,
	V128_ANY_TRUE = 0x53,
	I8x16_ABS = 0x60,
	I8x16_NEG = 0x61,
	I8x16_POPCNT = 0x62,
	I8x16_SHL = 0x6b,
	I8x16_SHR_S = 0x6c,
	I8x16_SHR_U = 0x6d,
	I8x16_ADD = 0x6e,
	I8x16_SUB = 0x71,
	I8x16_MIN_S = 0x76,
	I8x16_MIN_U = 0x77,
	I8x16_MAX_S = 0x78,
	I8x16_MAX_U = 0x79,
	I8x16_AVGR_U = 0x7b,
	I16x8_ABS = 0x80,
	I16x8_NEG = 0x81,
	I16x8_SHL = 0x8b,
	I16x8_SHR_S = 0x8c,
	I16x8_SHR_U = 0x8d,
	I16x8_ADD = 0x8e,
	I16x8_SUB = 0x91,
	I16x8_MUL = 0x95,
	I16x8_MIN_S = 0x96,
	I16x8_MIN_U = 0x97,
	I16x8_MAX_S = 0x98,
	I16x8_MAX_U = 0x99,
	I16x8_AVGR_U = 0x9b,
	I32x4_ABS = 0xa0,
	I32x4_NEG = 0xa1,
	I32x4_SHL = 0xab,
	I32x4_SHR_S = 0xac,
	I32x4_SHR_U = 0xad,
	I32x4_ADD = 0xae,
	I32x4_SUB = 0xb1,
	I32x4_MUL = 0xb5,
	I32x4_MIN_S = 0xb6,
	I32x4_MIN_U = 0xb7,
	I32x4_MAX_S = 0xb8,
	I32x4_MAX_U = 0xb9,
	I64x2_ABS = 0xc0,
	I64x2_NEG = 0xc1,
	I64x2_SHL = 0xcb,
	I64x2_SHR_S = 0xcc,
	I64x2_SHR_U = 0xcd,
	I64x2_ADD = 0xce,
	I64x2_SUB = 0xd1,
	I64x2_MUL = 0xd5,
	I64x2_EQ = 0xd6,
	I64x2_NE = 0xd7,
	I64x2_LT_S = 0xd8,
	I64x2_GT_S = 0xd9,
	I64x2_LE_S = 0xda,
	I64x2_GE_S = 0xdb,
	F32x4_ABS = 0xe0,
	F32x4_NEG = 0xe1,
	F32x4_SQRT = 0xe3,
	F32x4_ADD = 0xe4,
	F32x4_SUB = 0xe5,
	F32x4_MUL = 0xe6,
	F32x4_DIV = 0xe7,
	F32x4_MIN = 0xe8,
	F32x4_MAX = 0xe9,
	F64x2_ABS = 0xec,
	F64x2_NEG = 0xed,
	F64x2_SQRT = 0xef,
	F64x2_ADD = 0xf0,
	F64x2_SUB = 0xf1,
	F64x2_MUL = 0xf2,
	F64x2_DIV = 0xf3,
	F64x2_MIN = 0xf4,
	F64x2_MAX = 0xf5,
};

enum class WasmSIMDU32Opcode {
	I8x16_EXTRACT_LANE_S = 0x15,
	I8x16_EXTRACT_LANE_U = 0x16,
	I8x16_REPLACE_LANE = 0x17,
	I16x8_EXTRACT_LANE_S = 0x18,
	I16x8_EXTRACT_LANE_U = 0x19,
	I16x8_REPLACE_LANE = 0x1a,
	I32x4_EXTRACT_LANE = 0x1b,
	I32x4_REPLACE_LANE = 0x1c,
	I64x2_EXTRACT_LANE = 0x1d,
	I64x2_REPLACE_LANE = 0x1e,
	F32x4_EXTRACT_LANE = 0x1f,
	F32x4_REPLACE_LANE = 0x20,
	F64x2_EXTRACT_LANE = 0x21,
	F64x2_REPLACE_LANE = 0x22,
};

enum class WasmSIMDU32U32Opcode {
	V128_LOAD = 0x0,
	V128_LOAD8x8_S = 0x1,
	V128_LOAD8x8_U = 0x2,
	V128_LOAD16x4_S = 0x3,
	V128_LOAD16x4_U = 0x4,
	V128_LOAD32x2_S = 0x5,
	V128_LOAD32x2_U = 0x6,
	V128_STORE = 0x0b,
};

enum class WasmInvalidOpcode {
	BRANCH_LIKELY = 0x14,
	BRANCH_UNLIKELY = 0x15,
};


#endif // _CHEERP_WASM_OPCODES_H
