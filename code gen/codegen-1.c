/* codgen.c       Generate Assembly Code for x86         07 May 18   */

/* Copyright (c) 2018 Gordon S. Novak Jr. and The University of Texas at Austin
    */

/* Starter file for CS 375 Code Generation assignment.           */
/* Written by Gordon S. Novak Jr.                  */

/* This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License (file gpl.text) for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA. */

#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>
#include "token.h"
#include "symtab.h"
#include "lexan.h"
#include "genasm.h"
#include "codegen.h"
#include "pprint.h"

void genc(TOKEN code);

/* Set DEBUGGEN to 1 for debug printouts of code generation */
#define DEBUGGEN 0

int nextlabel;    /* Next available label number */
int stkframesize;   /* total stack frame size */
int* regs = NULL;  // register array
int numused;       // num of used registers

/* Top-level entry for code generator.
   pcode    = pointer to code:  (program foo (output) (progn ...))
   varsize  = size of local storage in bytes
   maxlabel = maximum label number used so far

Add this line to the end of your main program:
    gencode(parseresult, blockoffs[blocknumber], labelnumber);
The generated code is printed out; use a text editor to extract it for
your .s file.
         */

void gencode(TOKEN pcode, int varsize, int maxlabel) {  
  if (regs == NULL) {
    regs = malloc(32 * sizeof(int));
    clearreg();
  }
  TOKEN name, code;
  name = pcode->operands;
  code = name->link->link;
  nextlabel = maxlabel + 1;
  stkframesize = asmentry(name->stringval,varsize);
  genc(code);
  asmexit(name->stringval);
}

/* Trivial version: always returns RBASE + 0 */
/* Get a register.   */
/* Need a type parameter or two versions for INTEGER or REAL */
int getreg(int kind) {
    /*     ***** fix this *****   */
  if (kind  == WORD || kind == ADDR) {
    for (int i = RBASE; i <= RMAX; i++) {
      if (regs[i] == 0) {
        regs[i] = 1;
        return i;
      }
    }
  }
  if (kind == FLOAT) {
    for (int i = FBASE; i <= FMAX; i++) {
      if (regs[i] == 0) {
        regs[i] = 1;
        return i;
      }
    }
  }
  // reach here need to handle case that no register is available
  printf("not enough registers\n");
  return RBASE;
}
int getjmp(TOKEN code) {
  int out = -1;
  if (code->whichval == NEOP) out = JNE;
  else if (code->whichval == LEOP) out = JLE;
  else if (code->whichval == EQOP) out = JE;
  assert(out != -1);
  return out;
}

int getinst(TOKEN code) {
  int out = -1;
  if (code->basicdt == INTEGER) {
    if (code->whichval == PLUSOP) out = ADDL;
    else if (code->whichval == MINUSOP) out = SUBL;
    else if (code->whichval == TIMESOP) out = IMULL;
    else if (code->whichval == DIVIDEOP) out = DIVL;
  } 
  else if (code->basicdt == REAL) {
    if (code->whichval == PLUSOP) out = ADDSD;
    else if (code->whichval == MINUSOP) out = SUBSD;
    else if (code->whichval == TIMESOP) out = MULSD;
    else if (code->whichval == DIVIDEOP) out = DIVSD;
  }
  else if (code->basicdt == BOOLETYPE) {
    if (code->whichval == NEOP && code->operands->basicdt == POINTER) out = CMPQ; // check type of lhs and rhs maybe
    if (code->whichval == LEOP && code->operands->basicdt == INTEGER) out = CMPL;
    if (code->whichval == EQOP && code->operands->basicdt == INTEGER) out = CMPL;
  }
  assert(out != -1);
  return out;
}

int unary(TOKEN code, int reg1) {
  int reg2;
  if (code->whichval == FLOATOP) {
    reg2 = getreg(FLOAT);
    asmfloat(reg1, reg2);
    return reg2;
  }
  else if (code->whichval == FIXOP) {
    reg2 = getreg(WORD);
    asmfix(reg1, reg2);
    return reg2;
  } else if (code->whichval == MINUSOP) {
    if (code->basicdt == INTEGER) {
      printf("worry later\n");
    } else if (code->basicdt == REAL) {
      asmfneg(reg1, getreg(FLOAT));
      return reg1;
    }
  }
}


int funcallin(TOKEN code) {
  if (code == NULL) return 0;
  if (code->tokentype == OPERATOR && code->whichval == FUNCALLOP) return 1;
  if (funcallin(code->link)) return 1;
  if (funcallin(code->operands)) return 1;
  
}

/* Generate code for array references and pointers */
/* In Pascal, a (^ ...) can only occur as first argument of an aref. */
/* If storereg < 0, generates a load and returns register number;
   else, generates a store from storereg. */
int genaref(TOKEN code, int storereg) {
  assert(code->whichval == AREFOP);
  SYMBOL sym;
  sym = code->operands->symentry;
  
  if (sym != NULL) {
    if (sym->datatype) {
      if (sym->datatype->kind == POINTERSYM) {
        TOKEN arr = code->operands->operands;
        int r = getreg(WORD);
        if (storereg >= 0) {
          asmld(MOVQ, arr->symentry->offset - stkframesize, r, arr->stringval);
          asmstr(MOVL, storereg, arr->symentry->offset, r, "^. ");
          return r;
        } else {
          asmld(MOVQ,  arr->symentry->offset - stkframesize, r, arr->stringval);
          int r4 = getreg(WORD);
          asmldr(MOVL, r, arr->symentry->offset, r4, ".^ ");
          return r4;
        }
      }
    }
  }

  int r2 = getreg(WORD);
  asmimmed(MOVL, code->operands->link->intval, r2);
  asmop(CLTQ);
  if (storereg >= 0) {
    asmstrr(MOVSD, storereg, sym->offset - stkframesize, r2, code->operands->stringval);
  } else {
    int r3 = getreg(FLOAT);
    asmldrr(MOVSD, sym->offset - stkframesize, r2, r3, code->operands->stringval);
    return r3;
  }
}

/* Trivial version */
/* Generate code for arithmetic expression, return a register number */
// pointers need integer register
// post order traversal of expression tree. 
int genarith(TOKEN code) {
  int num, label;
  int reg1, reg2, inst;
  double fl;
  if (DEBUGGEN) { 
    printf("genarith\n");
	  dbugprinttok(code);
  };

  if (code->operands) {
    reg1 = genarith(code->operands);
    if (code->operands->link) reg2 = genarith(code->operands->link);
    else {
      return unary(code, reg1);
    }
    inst = getinst(code);
    asmrr(inst, reg2, reg1);
    return reg1;
  }

  if (code->operands == NULL) { // leaf node
    switch ( code->tokentype ) { 
      case NUMBERTOK:
        switch (code->basicdt) { 
          case INTEGER:
            num = code->intval;
            reg1 = getreg(WORD);
            if ( num >= MINIMMEDIATE && num <= MAXIMMEDIATE )
              asmimmed(MOVL, num, reg1);
            break;
          case REAL:
    /*     ***** fix this *****   */
            fl = code->realval;
            reg1 = getreg(FLOAT);
            label = nextlabel++;
            makeflit(fl, label);
            asmldflit(MOVSD,label,reg1);
            break;
          case POINTER:
            reg1 = getreg(ADDR);
            if (code->intval == 0) { // nil
              asmimmed(MOVQ, 0, reg1);
            }
            break;
        }
        break;
      case STRINGTOK:
        printf("string expression this is probs an arg to a function\n");
        break;
      case IDENTIFIERTOK:
        if (code->symentry) { // check if variable
          assert(code->symentry != NULL);
          if (code->symentry->basicdt == POINTER) {
            reg1 = getreg(ADDR);
            asmld(MOVQ, code->symentry->offset - stkframesize, reg1, code->stringval);
          }
          if (code->symentry->basicdt == INTEGER) {
            reg1 = getreg(WORD);
            asmld(MOVL, code->symentry->offset - stkframesize, reg1, code->stringval);
          }
          if (code->symentry->basicdt == REAL) {
            reg1 = getreg(FLOAT);
            asmld(MOVSD, code->symentry->offset - stkframesize, reg1, code->stringval);
          }
        }
    /*     ***** fix this *****   */
        break;
      case OPERATOR: // generate result into lhs register
      /*     ***** fix this *****   */

        break;
    };
    return reg1;
  }
}
// set all registers to unused
void clearreg() {
  for (int i = RBASE; i <= RMAX; i++) regs[i] = 0;
  for (int i = FBASE; i <= FMAX; i++) regs[i] = 0;
}

int genfun(TOKEN code) {
  int reg;
  TOKEN tok;
  tok = code->operands->link;
    while (tok != NULL) {
      reg = genarith(tok);
      if (tok->basicdt == INTEGER) asmrr(MOVL, reg, EDI);
      else if (tok->basicdt == STRINGTYPE) printf("strarg\n");
      tok = tok->link;
    }
  asmcall(code->operands->stringval);
  if (code->basicdt == REAL) return reg;
}

/* Generate code for a Statement from an intermediate-code form */
void genc(TOKEN code) {  
  clearreg();
  numused = 0;
  TOKEN tok, lhs, rhs;
  int reg, offs;
  int label1, label2;
  SYMBOL sym;
  if (DEBUGGEN) { 
    printf("genc\n");
	  dbugprinttok(code);
  };
  if ( code->tokentype != OPERATOR ) { 
    printf("Bad code token");
	  dbugprinttok(code);
	};
  switch ( code->whichval ) { 
    case PROGNOP:
	    tok = code->operands;
	    while ( tok != NULL )  {  
        genc(tok);
		    tok = tok->link;
	    };
	    break;
	  case ASSIGNOP:                   /* Trivial version: handles I := e */
	    lhs = code->operands;
	    rhs = lhs->link;
      if (funcallin(rhs)) {
        reg = genfun(rhs);
      } else if (rhs->tokentype == OPERATOR && rhs->whichval == AREFOP) {reg = genaref(rhs, -1);}
        else reg = genarith(rhs);              /* generate rhs into a register */
      if (code->basicdt == INTEGER || code->basicdt == REAL || code->basicdt == POINTER) {
        if (lhs->whichval == AREFOP) {
          genaref(lhs, reg);
          break;
        }
        


	      sym = lhs->symentry;              /* assumes lhs is a simple var  */
        assert(sym != NULL);
	      offs = sym->offset - stkframesize; /* net offset of the var   */
          switch (code->basicdt) {        /* store value into lhs  */ 
            case INTEGER:
              asmst(MOVL, reg, offs, lhs->stringval);
              break;
            case REAL:
              asmst(MOVSD,reg,offs, lhs->stringval );
              break;
            case POINTER:
              asmst(MOVQ,reg,offs,lhs->stringval);
              break;
          };
      }
      break;
	  case FUNCALLOP:
      tok = code->operands->link;
      while (tok != NULL) {
        reg = genarith(tok);
        if (tok->basicdt == INTEGER) asmrr(MOVL, reg, EDI);
        else if (tok->basicdt == STRINGTYPE) printf("strarg\n");
        tok = tok->link;
      }
      asmcall(code->operands->stringval);
      
    /*     ***** fix this *****   */
	    break;
	  case GOTOOP:
      asmjump(JMP, code->operands->intval);
    /*     ***** fix this *****   */
	    break;
	  case LABELOP:
      asmlabel(code->operands->intval);
    /*     ***** fix this *****   */
	    break;
	  case IFOP:
      genarith(code->operands);
      label1 = nextlabel++;
      label2 = nextlabel++;
      asmjump(getjmp(code->operands), label1);
      if (code->operands->link->link) genc(code->operands->link->link);
      asmjump(JMP, label2);
      asmlabel(label1);
      genc(code->operands->link);
      asmlabel(label2);
      
      
    /*     ***** fix this *****   */
	    break;
	};
}
