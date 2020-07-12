/*
** DynASM ARM encoding engine.
** Copyright (C) 2005-2017 Mike Pall. All rights reserved.
** Copyright (C) 2019 Andy Martin. All rights reserved.
** Released under the MIT license. See dynasm.lua for full copyright notice.
*/

#include <stddef.h>
#include <stdarg.h>
#include <string.h>
#include <stdlib.h>
#include <stdint.h>
#include "dasm_proto.h"

#define DASM_ARCH    "armv7m"

#ifndef DASM_EXTERN
#define DASM_EXTERN(a,b,c,d)        0
#endif

/* Endianness checks */
enum
{
    DASM_TARGET_BIG_ENDIAN,
    DASM_TARGET_LITTLE_ENDIAN
};

static int dasm_get_endianness()
{
    short int number = 0x1;
    char *numPtr = (char*)&number;
    return (numPtr[0] == 1) ? DASM_TARGET_LITTLE_ENDIAN : DASM_TARGET_BIG_ENDIAN;
}

/* Action definitions. */
enum {
  DASM_STOP, DASM_SECTION, DASM_ESC, DASM_REL_EXT,
  /* The following actions need a buffer position. */
  DASM_ALIGN, DASM_REL_LG, DASM_LABEL_LG,
  /* The following actions also have an argument. */
  DASM_REL_PC, DASM_LABEL_PC, DASM_REL_APC,
  DASM_IMM, DASM_IMM12, DASM_IMM16, DASM_IMM32,
  DASM_IMML, DASM_IMMV8, DASM_IMMSHIFT,
  /* The following actions have two arguments. */
  DASM_VRLIST,
  DASM__MAX
};

/* Maximum number of section buffer positions for a single dasm_put() call. */
#define DASM_MAXSECPOS                25

/* Macros to convert positions (8 bit section + 24 bit index). */
#define DASM_POS2IDX(pos)    ((pos)&0x00ffffff)
#define DASM_POS2BIAS(pos)   ((pos)&0xff000000)
#define DASM_SEC2POS(sec)    ((sec)<<24)
#define DASM_POS2SEC(pos)    ((pos)>>24)
#define DASM_POS2PTR(D, pos) (D->sections[DASM_POS2SEC(pos)].rbuf + (pos))

/* Action list type. */
typedef const unsigned int *dasm_ActList;

/* Per-section structure. */
typedef struct dasm_Section {
  int *rbuf;       /* Biased buffer pointer (negative section bias). */
  int *buf;        /* True buffer pointer. */
  size_t bsize;    /* Buffer size in bytes. */
  int pos;         /* Biased buffer position. */
  int epos;        /* End of biased buffer position - max single put. */
  int ofs;         /* Byte offset into section. */
} dasm_Section;

/* Core structure holding the DynASM encoding state. */
struct dasm_State {
  size_t psize;             /* Allocated size of this structure. */
  dasm_ActList actionlist;  /* Current actionlist pointer. */
  int *lglabels;            /* Local/global chain/pos ptrs. */
  size_t lgsize;
  int *pclabels;            /* PC label chains/pos ptrs. */
  size_t pcsize;
  void **globals;           /* Array of globals (bias -10). */
  dasm_Section *section;    /* Pointer to active section. */
  size_t codesize;          /* Total size of all code sections. */
  int maxsection;           /* 0 <= sectionidx < maxsection. */
  int status;               /* Status code. */
  int endianness;           /* Target endianness. */
  dasm_Section sections[1]; /* All sections. Alloc-extended. */
};

/* The size of the core structure depends on the max. number of sections. */
#define DASM_PSZ(ms)        (sizeof(dasm_State)+(ms-1)*sizeof(dasm_Section))


/* Initialize DynASM state. */
DASM_FDEF void dasm_init(Dst_DECL, int maxsection)
{
  dasm_State *D;
  size_t psz = 0;
  int i;
  Dst_REF = NULL;
  DASM_M_GROW(Dst, struct dasm_State, Dst_REF, psz, DASM_PSZ(maxsection));
  D = Dst_REF;
  D->psize = psz;
  D->lglabels = NULL;
  D->lgsize = 0;
  D->pclabels = NULL;
  D->pcsize = 0;
  D->globals = NULL;
  D->maxsection = maxsection;
  D->endianness = dasm_get_endianness();
  for (i = 0; i < maxsection; i++) {
    D->sections[i].buf = NULL;  /* Need this for pass3. */
    D->sections[i].rbuf = D->sections[i].buf - DASM_SEC2POS(i);
    D->sections[i].bsize = 0;
    D->sections[i].epos = 0;  /* Wrong, but is recalculated after resize. */
  }
}

/* Free DynASM state. */
DASM_FDEF void dasm_free(Dst_DECL)
{
  dasm_State *D = Dst_REF;
  int i;
  for (i = 0; i < D->maxsection; i++)
    if (D->sections[i].buf)
      DASM_M_FREE(Dst, D->sections[i].buf, D->sections[i].bsize);
  if (D->pclabels) DASM_M_FREE(Dst, D->pclabels, D->pcsize);
  if (D->lglabels) DASM_M_FREE(Dst, D->lglabels, D->lgsize);
  DASM_M_FREE(Dst, D, D->psize);
}

/* Setup global label array. Must be called before dasm_setup(). */
DASM_FDEF void dasm_setupglobal(Dst_DECL, void **gl, unsigned int maxgl)
{
  dasm_State *D = Dst_REF;
  D->globals = gl - 10;  /* Negative bias to compensate for locals. */
  DASM_M_GROW(Dst, int, D->lglabels, D->lgsize, (10+maxgl)*sizeof(int));
}

/* Grow PC label array. Can be called after dasm_setup(), too. */
DASM_FDEF void dasm_growpc(Dst_DECL, unsigned int maxpc)
{
  dasm_State *D = Dst_REF;
  size_t osz = D->pcsize;
  DASM_M_GROW(Dst, int, D->pclabels, D->pcsize, maxpc*sizeof(int));
  memset((void *)(((unsigned char *)D->pclabels)+osz), 0, D->pcsize-osz);
}

/* Setup encoder. */
DASM_FDEF void dasm_setup(Dst_DECL, const void *actionlist)
{
  dasm_State *D = Dst_REF;
  int i;
  D->actionlist = (dasm_ActList)actionlist;
  D->status = DASM_S_OK;
  D->section = &D->sections[0];
  memset((void *)D->lglabels, 0, D->lgsize);
  if (D->pclabels) memset((void *)D->pclabels, 0, D->pcsize);
  for (i = 0; i < D->maxsection; i++) {
    D->sections[i].pos = DASM_SEC2POS(i);
    D->sections[i].ofs = 0;
  }
}


#ifdef DASM_CHECKS
#define CK(x, st) \
  do { if (!(x)) { \
    D->status = DASM_S_##st|(p-D->actionlist-1); return; } } while (0)
#define CKPL(kind, st) \
  do { if ((size_t)((char *)pl-(char *)D->kind##labels) >= D->kind##size) { \
    D->status = DASM_S_RANGE_##st|(p-D->actionlist-1); return; } } while (0)
#else
#define CK(x, st)        ((void)0)
#define CKPL(kind, st)        ((void)0)
#endif

static int dasm_imm12(unsigned int n)
{
  unsigned int m = n;

  // v7M i:imm3 logic taken from https://github.com/jturnsek/LuaJIT/
  if (m <= 255) {
    /* i:imm3 = 0000 */
    return (m & 0xFF);
  }
  else if ((m & 0xff00ff00) == 0 && (((m >> 16) ^ m) & 0xff) == 0) {
    /* i:imm3 = 0001 */
    return (m & 0xFF) | (0x01 << 12);
  }
  else if ((m & 0x00ff00ff) == 0 && (((m >> 16) ^ m) & 0xff00) == 0) {
    /* i:imm3 = 0010 */
    return ((m >> 8) & 0xFF) | (0x02) << 12;
  }
  else if (((((m >> 16) & 0xffff) ^ m) & 0xffff) == 0 && ((((m >> 8) & 0xff) ^ m) & 0xff) == 0) {
    /* i:imm3 = 0011 */
    return ((m >> 8) & 0xFF) | (0x03) << 12;
  }
  else {
    for (unsigned int i = 0; i < 32; ++i, m = ((m << 1) | (m >> 31))) {
      if (m <= 255 && (m & 0x80) != 0)
        return (m & 0x7F) | ((i & 0x1) << 7) | ((i & 0xE) << (12 - 1)) | ((i & 0x10) << (26 - 4));
    }
  }
  return -1;
}

/* Pass 1: Store actions and args, link branches/labels, estimate offsets. */
DASM_FDEF void dasm_put(Dst_DECL, int start, ...)
{
  va_list ap;
  dasm_State *D = Dst_REF;
  dasm_ActList p = D->actionlist + start;
  dasm_Section *sec = D->section;
  int pos = sec->pos, ofs = sec->ofs;
  int *b;

  if (pos >= sec->epos) {
    DASM_M_GROW(Dst, int, sec->buf, sec->bsize,
      sec->bsize + 2*DASM_MAXSECPOS*sizeof(int));
    sec->rbuf = sec->buf - DASM_POS2BIAS(pos);
    sec->epos = (int)sec->bsize/sizeof(int) - DASM_MAXSECPOS+DASM_POS2BIAS(pos);
  }

  b = sec->rbuf;
  b[pos++] = start;

  va_start(ap, start);
  while (1) {
    unsigned int ins = *p++;
    unsigned int action = (ins >> 16);
    if (action >= DASM__MAX) {
      ofs += 4;
    } else {
      int *pl;
      int n = action >= DASM_REL_PC ? va_arg(ap, int) : 0;
      int n2 = action >= DASM_VRLIST ? va_arg(ap, int) : 0;
      switch (action) {
      case DASM_STOP: goto stop;
      case DASM_SECTION:
        n = (ins & 255); CK(n < D->maxsection, RANGE_SEC);
        D->section = &D->sections[n]; goto stop;
      case DASM_ESC: p++; ofs += 4; break;
      case DASM_REL_EXT: break;
      case DASM_ALIGN: ofs += (ins & 255); b[pos++] = ofs; break;
      case DASM_REL_LG:
        n = (ins & 2047) - 10; pl = D->lglabels + n;
        /* Bkwd rel or global. */
        if (n >= 0) { CK(n>=10||*pl<0, RANGE_LG); CKPL(lg, LG); goto putrel; }
        pl += 10; n = *pl;
        if (n < 0) n = 0;  /* Start new chain for fwd rel if label exists. */
        goto linkrel;
      case DASM_REL_PC:
        pl = D->pclabels + n; CKPL(pc, PC);
      putrel:
        n = *pl;
        if (n < 0) {  /* Label exists. Get label pos and store it. */
          b[pos] = -n;
        } else {
      linkrel:
          b[pos] = n;  /* Else link to rel chain, anchored at label. */
          *pl = pos;
        }
        pos++;
        break;
      case DASM_LABEL_LG:
        pl = D->lglabels + (ins & 2047) - 10; CKPL(lg, LG); goto putlabel;
      case DASM_LABEL_PC:
        pl = D->pclabels + n; CKPL(pc, PC);
      putlabel:
        n = *pl;  /* n > 0: Collapse rel chain and replace with label pos. */
        while (n > 0) { int *pb = DASM_POS2PTR(D, n); n = *pb; *pb = pos;
        }
        *pl = -pos;  /* Label exists now. */
        b[pos++] = ofs;  /* Store pass1 offset estimate. */
        break;
      case DASM_IMM:
      case DASM_IMM16:
#ifdef DASM_CHECKS
        CK((n & ((1<<((ins>>10)&31))-1)) == 0, RANGE_I);
        if ((ins & 0x8000))
          CK(((n + (1<<(((ins>>5)&31)-1)))>>((ins>>5)&31)) == 0, RANGE_I);
        else
          CK((n>>((ins>>5)&31)) == 0, RANGE_I);
#endif
      case DASM_IMM32:
        b[pos++] = n;
        break;
      case DASM_IMMV8:
        CK((n & 3) == 0, RANGE_I);
        n >>= 2;
        /* fallthrough */
      case DASM_IMML:
        CK(n >= 0 ? ((n>>((ins>>5)&31)) == 0) :
                    (((-n)>>((ins>>5)&31)) == 0), RANGE_I);
        b[pos++] = n;
        break;
      case DASM_IMM12:
        CK(dasm_imm12((unsigned int)n) != -1, RANGE_I);
        b[pos++] = n;
        break;
      case DASM_REL_APC:
      case DASM_IMMSHIFT:
        b[pos++] = n;
        break;
      case DASM_VRLIST:
        CK(n >= 0 && n < 31 && n2 >= 0 && n2 < 31, RANGE_I);
        b[pos++] = n;
        b[pos++] = n2;
        break;
      }
    }
  }
stop:
  va_end(ap);
  sec->pos = pos;
  sec->ofs = ofs;
}
#undef CK

/* Pass 2: Link sections, shrink aligns, fix label offsets. */
DASM_FDEF int dasm_link(Dst_DECL, size_t *szp)
{
  dasm_State *D = Dst_REF;
  int secnum;
  int ofs = 0;

#ifdef DASM_CHECKS
  *szp = 0;
  if (D->status != DASM_S_OK) return D->status;
  {
    int pc;
    for (pc = 0; pc*sizeof(int) < D->pcsize; pc++)
      if (D->pclabels[pc] > 0) return DASM_S_UNDEF_PC|pc;
  }
#endif

  { /* Handle globals not defined in this translation unit. */
    int idx;
    for (idx = 20; idx*sizeof(int) < D->lgsize; idx++) {
      int n = D->lglabels[idx];
      /* Undefined label: Collapse rel chain and replace with marker (< 0). */
      while (n > 0) { int *pb = DASM_POS2PTR(D, n); n = *pb; *pb = -idx; }
    }
  }

  /* Combine all code sections. No support for data sections (yet). */
  for (secnum = 0; secnum < D->maxsection; secnum++) {
    dasm_Section *sec = D->sections + secnum;
    int *b = sec->rbuf;
    int pos = DASM_SEC2POS(secnum);
    int lastpos = sec->pos;

    while (pos != lastpos) {
      dasm_ActList p = D->actionlist + b[pos++];
      while (1) {
        unsigned int ins = *p++;
        unsigned int action = (ins >> 16);
        switch (action) {
        case DASM_STOP: case DASM_SECTION: goto stop;
        case DASM_ESC: p++; break;
        case DASM_REL_EXT: break;
        case DASM_ALIGN: ofs -= (b[pos++] + ofs) & (ins & 255); break;
        case DASM_REL_LG: case DASM_REL_PC: case DASM_REL_APC: pos++; break;
        case DASM_LABEL_LG: case DASM_LABEL_PC: b[pos++] += ofs; break;
        case DASM_IMM: case DASM_IMM12: case DASM_IMM16: case DASM_IMM32:
        case DASM_IMML: case DASM_IMMV8: case DASM_IMMSHIFT: pos++; break;
        case DASM_VRLIST: pos += 2; break;
        }
      }
      stop: (void)0;
    }
    ofs += sec->ofs;  /* Next section starts right after current section. */
  }

  D->codesize = ofs;  /* Total size of all code sections */
  *szp = ofs;
  return DASM_S_OK;
}

#ifdef DASM_CHECKS
#define CK(x, st) \
  do { if (!(x)) return DASM_S_##st|(p-D->actionlist-1); } while (0)
#else
#define CK(x, st)        ((void)0)
#endif


static inline unsigned int dasm_armv7m_encode(dasm_State* d, const unsigned int v)
{
  /* For bytes 3210, on ARMv7-M LE this should become 2301, BE should be 3210 */
  if (d->endianness == DASM_TARGET_LITTLE_ENDIAN)
    return (v >> 16) | ((v & 0xFFFFU) << 16);
  else
    return v;
}

/* Pass 3: Encode sections. */
DASM_FDEF int dasm_encode(Dst_DECL, void *buffer)
{
  dasm_State *D = Dst_REF;
  char *base = (char *)buffer;
  unsigned int *cp = (unsigned int *)buffer;
  int secnum;

  /* Encode all code sections. No support for data sections (yet). */
  for (secnum = 0; secnum < D->maxsection; secnum++) {
    dasm_Section *sec = D->sections + secnum;
    int *b = sec->buf;
    int *endb = sec->rbuf + sec->pos;

    while (b != endb) {
      dasm_ActList p = D->actionlist + *b++;
      while (1) {
        unsigned int ins = *p++;
        unsigned int action = (ins >> 16);
        int n  = (action >= DASM_ALIGN  && action < DASM__MAX) ? *b++ : 0;
        int n2 = (action >= DASM_VRLIST && action < DASM__MAX) ? *b++ : 0;
        switch (action) {
        case DASM_STOP: case DASM_SECTION: goto stop;
        case DASM_ESC:
          if (cp != buffer)
            cp[-1] = dasm_armv7m_encode(D, cp[-1]);
          *cp++ = *p++; break;
        case DASM_REL_EXT:
          n = DASM_EXTERN(Dst, (unsigned char *)cp, (ins&2047), !(ins&2048));
          goto patchrel;
        case DASM_ALIGN:
          ins &= 255;
          while ((((char *)cp - base) & ins)) {
            if (cp != buffer)
              cp[-1] = dasm_armv7m_encode(D, cp[-1]);
            *cp++ = 0xf3af8000; // NOP
          }
          break;
        case DASM_REL_LG:
          CK(n >= 0, UNDEF_LG);
          /* fallthrough */
        case DASM_REL_PC:
          CK(n >= 0, UNDEF_PC);
          n = *DASM_POS2PTR(D, n) - (int)((char *)cp - base);
        patchrel:
          if (ins & 32768) { /* branch */
            CK((n & 1) == 0 && -16777216 <= n && n < 16777216, RANGE_REL);
            goto patchbptr;
          } else if (ins & 16384) { /* vload IMM8:'00' */
            n /= 4;
          } else if (ins & 8192) { /* ADR */
            CK((n & 1) == 0 && -4096 < n && n < 4096, RANGE_REL);
            if (n < 0) {
              cp[-1] |= 0x00A00000;
              n = -n;
            }
            cp[-1] |= (n & 0xFF) | (((n >> 8) & 0x7) << 12) | (((n >> 11) & 0x1) << 26);
            break;
          }
          CK((n & 3) == 0 && -4096 <= n && n < 4096, RANGE_REL);
          goto patchimml;
        case DASM_LABEL_LG:
          ins &= 2047; if (ins >= 20) D->globals[ins-10] = (void *)(base + n);
          break;
        case DASM_LABEL_PC: break;
        case DASM_IMM:
          n2 = (ins >> 10) & 31; /* scale */
          if (ins & 0x8000) {
            /* *add/subtract* an offset to the runtime-found value instead of scaling */
            n += ((ins >> 10) & 0x10) ? -(((int)ins >> 10) & 0x0F) : (((int)ins >> 10) & 0x0F);
            n2 = 0;
          }
          /* *scale* the runtime-found value n down, restrict it to its *bits* count, then *shift* it up */
          cp[-1] |= ((n >> n2) & ((1 << ((ins >> 5) & 31)) - 1)) << (ins & 31);
          break;
        case DASM_IMM12:
          cp[-1] |= dasm_imm12((unsigned int)n);
          if (cp[-1] == 0xFFFFFFFF) return DASM_S_RANGE_I;
          break;
        case DASM_IMM16:
          cp[-1] |= (n & 0xFF) | (((n >> 8) & 0x7) << 12) | (((n >> 11) & 0x1) << 26) | (((n >> 12) & 0xF) << 16);
          break;
        case DASM_IMM32:
          cp[-1] |= n;
          break;
        case DASM_IMML: case DASM_IMMV8: patchimml:
          cp[-1] |= n >= 0 ? (0x00800000 | n) : (-n);
          break;
        case DASM_IMMSHIFT:
          cp[-1] |= (ins & 0xFFFF) << (n & 31);
          break;
        case DASM_VRLIST:
          n2 = (n2 + 1 - n);     /* nr = rb + 1 - ra */
          if ((ins & 0x1) == 0)  /* "s" registers */
            cp[-1] |= (((n & 31) >> 1) << 12) + ((n & 1) << 22) + n2;
          else                   /* "d" registers */
            cp[-1] |= ((n & 15) << 12) + (((n & 31) >> 4) << 22) + n2 * 2 + 0x100;
          break;
        case DASM_REL_APC:
          n -= (int)(intptr_t)cp - 4; /* n -= cp[-1] */
        patchbptr:
          (void)0;
          const unsigned int isimm10 = (ins & 16384);
          CK((n & 1) == 0 && (isimm10 ? -16777216 : -1048576) <= n && n <= (isimm10 ? 16777216 : 1048576), RANGE_REL);
          const unsigned int Sbit = (n < 0) & 0x1;
          const unsigned int imm11 = (n >> 1) & 0x7FF;
          const unsigned int immr = (((n >> 12) & (isimm10 ? 0x3FF : 0x3F)) << 16);
          cp[-1] |= imm11 | immr | (Sbit << 26);
          if (isimm10) {
            // I1 = NOT(J1 EOR S); I2 = NOT(J2 EOR S); imm32 = SignExtend(S:I1:I2:imm10:imm11:'0', 32);
            const unsigned int i1 = ((n >> 1) & (1 << 22)) >> 22;
            const unsigned int i2 = ((n >> 1) & (1 << 21)) >> 21;
            const unsigned int j1 = (~(Sbit ^ i1) & 0x1) << 13;
            const unsigned int j2 = (~(Sbit ^ i2) & 0x1) << 11;
            cp[-1] |= j1 | j2;
          } else {
            // imm32 = SignExtend(S:J2:J1:imm6:imm11:'0', 32);
            const unsigned int j1 = ((n >> 1) & (1 << 18)) >> (18 - 13);
            const unsigned int j2 = ((n >> 1) & (1 << 19)) >> (19 - 11);
            cp[-1] |= j1 | j2;
          }
          break;
        default:
          if (cp != buffer)
            cp[-1] = dasm_armv7m_encode(D, cp[-1]);
          *cp++ = ins; break;
        }
      }
    stop:
      (void)0;
    }
  }

  if (cp != buffer)
    cp[-1] = dasm_armv7m_encode(D, cp[-1]);

  if (base + D->codesize != (char *)cp)  /* Check for phase errors. */
    return DASM_S_PHASE;
  return DASM_S_OK;
}
#undef CK

/* Get PC label offset. */
DASM_FDEF int dasm_getpclabel(Dst_DECL, unsigned int pc)
{
  dasm_State *D = Dst_REF;
  if (pc*sizeof(int) < D->pcsize) {
    int pos = D->pclabels[pc];
    if (pos < 0) return *DASM_POS2PTR(D, -pos);
    if (pos > 0) return -1;  /* Undefined. */
  }
  return -2;  /* Unused or out of range. */
}

#ifdef DASM_CHECKS
/* Optional sanity checker to call between isolated encoding steps. */
DASM_FDEF int dasm_checkstep(Dst_DECL, int secmatch)
{
  dasm_State *D = Dst_REF;
  if (D->status == DASM_S_OK) {
    int i;
    for (i = 1; i <= 9; i++) {
      if (D->lglabels[i] > 0) { D->status = DASM_S_UNDEF_LG|i; break; }
      D->lglabels[i] = 0;
    }
  }
  if (D->status == DASM_S_OK && secmatch >= 0 &&
      D->section != &D->sections[secmatch])
    D->status = DASM_S_MATCH_SEC|(D->section-D->sections);
  return D->status;
}
#endif

