%{     /* pars1.y    Pascal Parser      Gordon S. Novak Jr.  ; 08 Jul 22   */

/* Copyright (c) 2022 Gordon S. Novak Jr. and
   The University of Texas at Austin. */

/* 14 Feb 01; 01 Oct 04; 02 Mar 07; 27 Feb 08; 24 Jul 09; 02 Aug 12;
   30 Jul 13; 25 Jul 19 ; 28 Feb 22 */

/*
; This program is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, see <http://www.gnu.org/licenses/>.
  */


/* NOTE:   Copy your lexan.l lexical analyzer to this directory.      */

       /* To use:
                     make pars1y              has 1 shift/reduce conflict
                     pars1y                   execute the parser
                     i:=j .
                     ^D                       control-D to end input

                     pars1y                   execute the parser
                     begin i:=j; if i+j then x:=a+b*c else x:=a*b+c; k:=i end.
                     ^D

                     pars1y                   execute the parser
                     if x+y then if y+z then i:=j else k:=2.
                     ^D

           You may copy pars1.y to be parse.y and extend it for your
           assignment.  Then use   make parser   as above.
        */

        /* Yacc reports 1 shift/reduce conflict, due to the ELSE part of
           the IF statement, but Yacc's default resolves it in the right way.*/

#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include <assert.h>
#include "token.h"
#include "lexan.h"
#include "symtab.h"
#include "parse.h"
#include "pprint.h"

        /* define the type of the Yacc stack element to be TOKEN */

#define YYSTYPE TOKEN

TOKEN parseresult;

%}

/* Order of tokens corresponds to tokendefs.c; do not change */

%token IDENTIFIER STRING NUMBER   /* token types */

%token PLUS MINUS TIMES DIVIDE    /* Operators */
%token ASSIGN EQ NE LT LE GE GT POINT DOT AND OR NOT DIV MOD IN

%token COMMA                      /* Delimiters */
%token SEMICOLON COLON LPAREN RPAREN LBRACKET RBRACKET DOTDOT

%token ARRAY BEGINBEGIN           /* Lex uses BEGIN */
%token CASE CONST DO DOWNTO ELSE END FILEFILE FOR FUNCTION GOTO IF LABEL NIL
%token OF PACKED PROCEDURE PROGRAM RECORD REPEAT SET THEN TO TYPE UNTIL
%token VAR WHILE WITH

%right thenthen ELSE // Same precedence, but "shift" wins.

%%

  program    :  PROGRAM IDENTIFIER LPAREN id_list RPAREN SEMICOLON cblock DOT
          /* change this! */       { parseresult = makeprogram($2, $4, $7);}
             ;
  block      :  BEGINBEGIN statement endpart {$$ = cons($2, $3);}
             ;
  
  statement  :  BEGINBEGIN statement endpart    
                                       {$$ = makeprogn($1,cons($2, $3));}
             |  IF expr THEN statement endif   { $$ = makeif($1, $2, $4, $5); }
             |  assignment                     { $$ = $1;}
             |  funcall                        { $$ = $1;}
             |  FOR IDENTIFIER ASSIGN expr TO expr DO statement {
                      $$ = makefor(0, $2, $3, $4, $6, $7, $8);}
             |  REPEAT st_list UNTIL expr      {makerepeat($1, $2, $3, $4);
                    }
             ;
  st_list    :  statement SEMICOLON st_list   {$$ = cons($1, $3);}
             |  statement                     {$$ = $1;}
             ;
  endpart    :  SEMICOLON statement endpart    { $$ = cons($2, $3);}
             |  END                            { $$ = NULL; }
             ;
  endif      :  ELSE statement                 { $$ = $2; }
             |  /* empty */                    { $$ = NULL; }  %prec thenthen
             ;
  assignment :  variable ASSIGN expr           { printf("ass %s\n",$1->stringval); $$ = binop($2, $1, $3); }
             ;
  expr       :  expr compare_op s_expr                 { $$ = binop($2, $1, $3); }
             |  s_expr                              {$$ = $1;}
             ;
  s_expr     :  sign term                   {$$ = unaryop($1, $2);}
             |  term                        {$$ = $1;}
             |  s_expr plus_op term         {$$ = binop($2, $1, $3);}
             ;
  expr_list  :  expr COMMA expr_list            {$$ = cons($1, $3);}
             |  expr                            {$$ = $1;}
             ;
  funcall    :  IDENTIFIER LPAREN expr_list RPAREN {$$ = makefuncall($2, $1, $3);}
             ;
  id_list    :  IDENTIFIER COMMA id_list       { $$ = cons($1, $3);}
             |  IDENTIFIER                     { $$ = $1;}
             ;
  term       :  term times_op factor              { $$ = binop($2, $1, $3); }
             |  factor                         { $$ = $1;}
             ;
  vblock     :  VAR vdef_list block            { $$ = $3;}
             ;
  vdef_list  :  vdef SEMICOLON vdef_list
             |  vdef SEMICOLON
             ;
  vdef       :  id_list COLON IDENTIFIER        {instvars($1, $3);}
             ;
  factor     :  LPAREN expr RPAREN             { $$ = $2; }
             |  funcall                        { $$ = $1; }
             |  variable                       { $$ = $1; }
             |  NUMBER                         { $$ = $1; }
             |  u_constant                     { $$ = $1;}
             ;
  variable   : IDENTIFIER                      { $$ = findid($1); }
             ;
  cdef       : IDENTIFIER EQ constant     {instconst($1, $3);} 
             ;
  cdef_list  : cdef SEMICOLON cdef_list
             | cdef
             |
             ;
  cblock     : CONST cdef_list vblock         {$$ = $3;}
             | vblock                         {$$ = $1;}
             ;
  times_op   : TIMES       {$$ = makeop(TIMESOP);}
             | DIVIDE      {$$ = makeop(DIVIDEOP);}
             | DIV         {$$ = makeop(DIVOP);}
             | MOD         {$$ = makeop(MODOP);}
             | AND         {$$ = makeop(ANDOP);}
             ;
  plus_op    : sign        {$$ = $1;}
             | OR          {$$ = makeop(OROP);}
             ;
  sign       : PLUS        {$$ = makeop(PLUSOP);} 
             | MINUS       {$$ = makeop(MINUSOP);}
             ;
  compare_op : EQ          {$$ = makeop(EQOP);}
             | LT          {$$ = makeop(LTOP);}
             | GT          {$$ = makeop(GTOP);}
             | NE          {$$ = makeop(NEOP);}
             | LE          {$$ = makeop(LEOP);}
             | GE          {$$ = makeop(GEOP);}
             | IN          {$$ = makeop(INOP);}
             ;
  constant   :  u_constant {$$ = $1;}
             |  sign IDENTIFIER    {$$ = unaryop($1, $2);}
             |  sign NUMBER        {$$ = unaryop($1, $2);}
             ;
  u_constant : NUMBER      {$$ = $1;}
             | NIL         
             | STRING      {$$ = $1;}
             ;

  
%%

/* You should add your own debugging flags below, and add debugging
   printouts to your programs.

   You will want to change DEBUG to turn off printouts once things
   are working.
  */

#define DEBUG        31             /* set bits here for debugging, 0 = off  */
#define DB_CONS       1             /* bit to trace cons */
#define DB_BINOP      2             /* bit to trace binop */
#define DB_MAKEIF     4             /* bit to trace makeif */
#define DB_MAKEPROGN  8             /* bit to trace makeprogn */
#define DB_PARSERES  16             /* bit to trace parseresult */

 int labelnumber = 0;  /* sequential counter for internal label numbers */

   /*  Note: you should add to the above values and insert debugging
       printouts in your routines similar to those that are shown here.     */

TOKEN cons(TOKEN item, TOKEN list)           /* add item to front of list */
  { item->link = list;
    if (DEBUG & DB_CONS)
       { printf("cons\n");
         dbugprinttok(item);
         dbugprinttok(list);
       };
    return item;
  }

TOKEN findid(TOKEN tok) { /* the ID token */
SYMBOL sym = searchst(tok->stringval);
if (sym != NULL) {
  if (sym->kind == CONSTSYM) {
    tok->basicdt = sym->basicdt;
    if (tok->basicdt == INTEGER || tok->basicdt == REAL) {
      tok->tokentype = NUMBERTOK;
      if (tok->basicdt == INTEGER) tok->intval = sym->constval.intnum;
      if (tok->basicdt == REAL) tok->realval = sym->constval.realnum;
    }
    return tok;
  }
}
tok->symentry = sym;
  SYMBOL typ = sym->datatype;
  tok->symtype = typ;
  if ( typ->kind == BASICTYPE || typ->kind == POINTERSYM)
    tok->basicdt = typ->basicdt;

return tok; }

TOKEN makerepeat(TOKEN tok, TOKEN statements, TOKEN tokb, TOKEN expr) {
  TOKEN lab = makeprogn(tok, makelabel());
  TOKEN gt = makegoto(labelnumber - 1);
  tokb = makeprogn(tokb, statements);
  TOKEN progtok = makeprogn(talloc(), NULL);
  progtok->link = gt;
  TOKEN iftok = makeif(talloc(), expr, progtok, gt);
  tokb->link = iftok;
  lab->operands->link = tokb;
  return lab;
}

TOKEN makefloat(TOKEN tok) {
  if (tok->tokentype == NUMBERTOK) {
    tok->basicdt = REAL;
    tok->realval = (double) tok->intval;
    return tok;
  } else {
    TOKEN out = makeop(FLOATOP);
    out->operands = tok;
    return out;
  }
}

TOKEN makefix(TOKEN tok) {
  if (tok->tokentype == NUMBERTOK) {
    tok->basicdt = INTEGER;
    tok->intval = (int) tok->realval;
    return tok;
  } else {
    TOKEN out = makeop(FIXOP);
    out->operands = tok;
    return out;
  }
}




TOKEN unaryop(TOKEN op, TOKEN lhs) {
  op->operands = lhs;
  return op;
}

TOKEN binop(TOKEN op, TOKEN lhs, TOKEN rhs)        /* reduce binary operator */
  { op->operands = lhs;          /* link operands to operator       */
    lhs->link = rhs;             /* link second operand to first    */
    rhs->link = NULL;            /* terminate operand list          */
    if (DEBUG & DB_BINOP)
       { printf("binop\n");
         dbugprinttok(op);
         dbugprinttok(lhs);
         dbugprinttok(rhs);
       };
 
    if (lhs->basicdt == REAL && rhs->basicdt == REAL) {
      op->basicdt = REAL;
    } else if (lhs->basicdt == INTEGER && rhs->basicdt == INTEGER){
      op->basicdt = INTEGER;
    } else if (lhs->basicdt == REAL && rhs->basicdt == INTEGER) {
      op->basicdt = REAL;
      TOKEN fl = makefloat(rhs);
      lhs->link = fl;
    } else if (lhs->basicdt == INTEGER && rhs->basicdt == REAL) {
      if (op->whichval == ASSIGNOP) {
        op->basicdt = INTEGER;
        TOKEN fx = makefix(rhs);
        lhs->link = fx;
      } else {
        op->basicdt = REAL;
        TOKEN fl = makefloat(lhs);
        fl->link = rhs;
      }
    }

    return op;
  }

TOKEN makeif(TOKEN tok, TOKEN exp, TOKEN thenpart, TOKEN elsepart)
  {  tok->tokentype = OPERATOR;  /* Make it look like an operator   */
     tok->whichval = IFOP;
     if (elsepart != NULL) elsepart->link = NULL;
     thenpart->link = elsepart;
     exp->link = thenpart;
     tok->operands = exp;
     if (DEBUG & DB_MAKEIF)
        { printf("makeif\n");
          dbugprinttok(tok);
          dbugprinttok(exp);
          dbugprinttok(thenpart);
          dbugprinttok(elsepart);
        };
     return tok;
   }

TOKEN makeprogn(TOKEN tok, TOKEN statements)
  {  tok->tokentype = OPERATOR;
     tok->whichval = PROGNOP;
     tok->operands = statements;
     if (DEBUG & DB_MAKEPROGN)
       { printf("makeprogn\n");
         dbugprinttok(tok);
         dbugprinttok(statements);
       };
     return tok;
   }

TOKEN makeprogram(TOKEN name, TOKEN args, TOKEN statements) {
  TOKEN prog = talloc();
  prog->tokentype = OPERATOR;
  prog->whichval = PROGRAMOP;
  prog->operands = name;
  name->link = makeprogn(talloc(), args);
  name->link->link = makeprogn(talloc(), statements);
  return prog;
}

int wordaddress(int n, int wordsize)
  { return ((n + wordsize - 1) / wordsize) * wordsize; }
 
void yyerror (char const *s)
{
  fprintf (stderr, "%s\n", s);
}

TOKEN makefuncall(TOKEN tok, TOKEN fn, TOKEN args) {
  tok->tokentype = OPERATOR;
  tok->whichval = FUNCALLOP;
  tok->operands = fn;
  fn->link = args;
  SYMBOL f = searchst(fn->stringval);
  tok->basicdt = f->datatype->basicdt;
  return tok;
}

TOKEN makegoto(int label) {
  TOKEN gt = talloc();
  gt->tokentype = OPERATOR;
  gt->whichval = GOTOOP;
  TOKEN l = makeintc(label);
  gt->operands = l;
  return gt;
}


// tok is id that is being assigned the expression tokb. asg is the asg operator
// endexpr is the limit of the loop, tokc is a do token, state is the loop body 
TOKEN makefor(int sign, TOKEN tok, TOKEN asg, TOKEN tokb, TOKEN endexpr,
              TOKEN tokc, TOKEN statement) {
    TOKEN id1 = copytok(tok);
    TOKEN id2 = copytok(tok);
    TOKEN id3 = copytok(tok);
    TOKEN lab = makelabel();
    // make tokc the loop condition
    tokc->tokentype = OPERATOR;
    tokc->whichval = LEOP;
    tokc = binop(tokc, id1, endexpr);
    TOKEN assign = binop(asg, tok, tokb);
    // make increment
    TOKEN inc = makeop(ASSIGNOP);
    TOKEN add = makeop(PLUSOP);
    TOKEN one = makeintc(1);
    add = binop(add, id2, one);
    inc = binop(inc, id3, add);
    TOKEN gt = makegoto(labelnumber - 1);
    inc->link = gt;
    statement->link = inc;
    statement = makeprogn(talloc(), statement);
    lab->link = makeif(talloc(), tokc, statement, NULL);
    assign->link = lab;    
    return makeprogn(talloc(), assign);
  }

  TOKEN makeintc(int num) {
    TOKEN t = talloc();
    t->tokentype = NUMBERTOK;
    t->basicdt = INTEGER;
    t->intval = num;
    return t;
  }

// assumes identifier copying
TOKEN copytok(TOKEN origtok) {
  TOKEN out = talloc();
  out->tokentype = origtok->tokentype;
  strcpy(out->stringval, origtok->stringval);
  return out;
}

TOKEN makeop(int opnum) {
  TOKEN out = talloc();
  out->tokentype = OPERATOR;
  out->whichval = opnum;
  return out;
}
              

TOKEN makelabel() {
  TOKEN lab = talloc();
  lab->tokentype = OPERATOR;
  lab->whichval = LABELOP;
  TOKEN num = makeintc(labelnumber);
  labelnumber++;
  lab->operands = num;
  return lab;  
}

void instvars(TOKEN idlist, TOKEN typetok)
  { SYMBOL sym, typesym; int align;
    typesym = searchst(typetok->stringval);
    align = alignsize(typesym);
    while ( idlist != NULL ) /* for each id */
      { sym = insertsym(idlist->stringval);
        sym->kind = VARSYM;
        sym->offset = /* "next" */
        wordaddress(blockoffs[blocknumber], align);
        sym->size = typesym->size;
        blockoffs[blocknumber] = sym->offset + sym->size;
        sym->datatype = typesym;
        sym->basicdt = typesym->basicdt;
        idlist = idlist->link;
};
}

void  instconst(TOKEN idtok, TOKEN consttok) {
  SYMBOL sym, typesym;
  sym = insertsym(idtok->stringval);
  sym->kind = CONSTSYM;
  sym->basicdt = consttok->basicdt;
  if (sym->basicdt == INTEGER) {
    sym->constval.intnum = consttok->intval;
  } else if (sym->basicdt == REAL) {
    sym->constval.realnum = consttok->realval;
  } else if (sym->basicdt ==  STRINGTYPE) {
    strcpy(sym->constval.stringconst, consttok->stringval);
  }
}


int main(void)          /*  */
  { int res;
    initsyms();
    res = yyparse();
    printst();       /* to shorten, change to:  printstlevel(1);  */
    printf("yyparse result = %8d\n", res);
    if (DEBUG & DB_PARSERES) dbugprinttok(parseresult);
    ppexpr(parseresult);           /* Pretty-print the result tree */
    /* uncomment following to call code generator. */
     /* 
    gencode(parseresult, blockoffs[blocknumber], labelnumber);
 */
  }