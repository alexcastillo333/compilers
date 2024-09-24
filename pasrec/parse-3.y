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
#include <float.h>
#include "token.h"
#include "lexan.h"
#include "symtab.h"
#include "parse.h"
#include "pprint.h"

        /* define the type of the Yacc stack element to be TOKEN */

#define YYSTYPE TOKEN

TOKEN parseresult;
int labels[10];

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

  program    :  PROGRAM IDENTIFIER LPAREN id_list RPAREN SEMICOLON lblock DOT
          /* change this! */       { parseresult = makeprogram($2, $4, $7);}
             ;
  block      :  BEGINBEGIN statement endpart {$$ = cons($2, $3);}
             ;
  lblock     :  LABEL numlist SEMICOLON cblock      {$$ = $4;}
             |  cblock                               {$$ = $1;}
             ;
  numlist    :  NUMBER COMMA numlist    {instlabel($1);}      
             |  NUMBER                  {instlabel($1);}
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
             | NUMBER COLON statement   {$$ = dolabel($1, $2, $3);}
             | WHILE expr DO statement  {$$ = makewhile($1, $2, $3, $4);}
             | GOTO NUMBER              {$$ = dogoto($1, $2);}
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
  assignment :  variable ASSIGN expr           { $$ = binop($2, $1, $3); }
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
  vblock     :  VAR vdef_list block            {  $$ = $3;}
             ;
  vdef_list  :  vdef SEMICOLON vdef_list
             |  vdef SEMICOLON
             ;
  vdef       :  id_list COLON type        {instvars($1, $3);}
             ;
  factor     :  LPAREN expr RPAREN             { $$ = $2; }
             |  funcall                        { $$ = $1; }
             |  variable                       { $$ = $1; }
             |  NUMBER                         { $$ = $1; }
             |  u_constant                     { $$ = $1;}
             |  NIL                            {   
                  TOKEN makenil(); $$ = makenil();}
             ;
  variable   : IDENTIFIER                      { $$ = findid($1); }
             | variable DOT IDENTIFIER         { $$ = reducedot($1, $2, $3); }
             | variable LBRACKET expr_list RBRACKET { $$ = arrayref($1, $2, $3, $4);}
             | variable POINT                      {$$ = dopoint($1, $2);}
             ;
  cdef       : IDENTIFIER EQ constant     {instconst($1, $3);} 
             ;
  cdef_list  : cdef SEMICOLON cdef_list
             | cdef
             |
             ;
  cblock     : CONST cdef_list tblock         {$$ = $3;}
             | tblock                         {$$ = $1;}
             ;
  tblock     : TYPE tdef_list vblock      {$$ = $3;}
             | vblock                      {$$ = $1;}
             ;
  tdef_list  : tdef SEMICOLON tdef_list
             | tdef SEMICOLON
             ;
  tdef       : IDENTIFIER EQ type         {insttype($1, $3);}
             ;
  type       : simple_type                {}
             | ARRAY LBRACKET simple_type_list RBRACKET OF type {$$ = instarray($3, $6);}
             | RECORD field_list END            {$$ = instrec($1, $2);}
             | POINT IDENTIFIER                 {$$ = instpoint($1, $2);}
             ;
  fields     : id_list COLON type             {$$ = instfields($1, $3);}
             ;
  field_list : fields SEMICOLON field_list    {$$ = nconc($1, $3);}
             | fields                         {$$ = $1;}
             ;
  simple_type: IDENTIFIER       {$$ = findtype($1);}
             | LPAREN id_list RPAREN    {$$ = instenum($2);}
             | constant DOTDOT constant {$$ = instdotdot($1 ,$2, $3);}
             ;
  simple_type_list : simple_type COMMA simple_type_list {$$ = cons($1, $3);}
             | simple_type      {$$ = $1;}
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
             | STRING      {$1->basicdt = STRINGTYPE; $$ = $1;}
             ;

  
%%

/* You should add your own debugging flags below, and add debugging
   printouts to your programs.

   You will want to change DEBUG to turn off printouts once things
   are working.
  */

#define DEBUG        0            /* set bits here for debugging, 0 = off  */
#define DB_CONS       1             /* bit to trace cons */
#define DB_BINOP      2             /* bit to trace binop */
#define DB_MAKEIF     4             /* bit to trace makeif */
#define DB_MAKEPROGN  8             /* bit to trace makeprogn */
#define DB_PARSERES  16             /* bit to trace parseresult */

 int labelnumber = 0;  /* sequential counter for internal label numbers */

   /*  Note: you should add to the above values and insert debugging
       printouts in your routines similar to those that are shown here.     */

TOKEN makenil() {
  TOKEN t = talloc();
  t->tokentype = NUMBERTOK;
  t->basicdt = POINTER;
  t->intval = 0;
  return t;
}

TOKEN dogoto(TOKEN tok, TOKEN labeltok) {
  tok = makeop(GOTOOP);
  int l;
  for (int i = 0; i < 10; i++) {
    if (labels[i] == labeltok->intval) {
      l = i;
    }
  }
  tok->operands = makeintc(l);
  return tok;
}


TOKEN cons(TOKEN item, TOKEN list)           /* add item to front of list */
  { item->link = list;
    if (DEBUG & DB_CONS)
       { printf("cons\n");
         dbugprinttok(item);
         dbugprinttok(list);
       };
    return item;
  }

TOKEN dolabel(TOKEN labeltok, TOKEN tok, TOKEN statement) {
  TOKEN prog = makeop(PROGNOP);
  TOKEN lab = makeop(LABELOP);
  int l = -1;
  for(int i = 0; i < 10; i++) {
    if (labels[i] == labeltok->intval) l = i;
  }
  lab->operands = makeintc(l);
  lab->link = statement;
  prog->operands = lab;
  return prog;
}

TOKEN instpoint(TOKEN tok, TOKEN typename) {
	SYMBOL ptr, sym;
  tok->basicdt = POINTER;
	ptr = symalloc();
	ptr->kind = POINTERSYM;
	ptr->basicdt = POINTER;
	ptr->size = basicsizes[POINTER];
	tok->symtype = ptr;
	sym = searchins(typename->stringval);
  if (sym->kind != BASICTYPE) {
	  sym->kind = TYPESYM;
  }
  ptr->datatype = sym;
	return tok;
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

TOKEN instdotdot(TOKEN lowtok, TOKEN dottok, TOKEN hightok) {
  return makesubrange(dottok, lowtok->intval, hightok->intval);
}

TOKEN reducedot(TOKEN var, TOKEN dot, TOKEN field) {
  assert(var->symtype->kind == RECORDSYM);
  TOKEN out;
  SYMBOL s = var->symtype;
  SYMBOL ss = NULL;
  int old;
  s = s->datatype;
  while (s) {
    if (strcmp(s->namestring, field->stringval) == 0) {
      if (var->whichval == AREFOP) {
        if ((ss = var->symentry) && ss->kind == ARRAYSYM) {
          var->operands->link->operands->intval += s->offset;
        } else {
          var->operands->link->intval += s->offset;
        }
        var->basicdt = s->basicdt;
        var->symtype = s->datatype;
        if (s->datatype) {
          if (s->datatype->datatype) {
            var->symtype = s->datatype->datatype;
          }
        }
        return var;
      }
      out = makearef(var, makeintc(s->offset), dot);
      out->basicdt = s->basicdt;
      out->symtype = s->datatype;
      if (s->datatype) {
        if (s->datatype->datatype) {
          out->symtype = s->datatype->datatype;
        }
      } 
      return out;
    }
    s = s->link;
  }
}


TOKEN reducedotold(TOKEN var, TOKEN dot, TOKEN field) {
  SYMBOL s;
  TOKEN out;
	if (var->whichval == POINTEROP) {
		if (searchst(var->operands->stringval) != NULL) {
      s = var->symtype->datatype;
      while(s) {
        if (strcmp(s->namestring, field->stringval) == 0) {
          out = makearef(var, makeintc(s->offset), dot);
          if (s->basicdt == REAL) {
            out->basicdt = REAL;
            return out;
          }
          return out;
        }
        s = s->link;
      }
    } else {
      s = var->symtype->datatype;
      while (s) {
        if (strcmp(s->namestring, field->stringval) == 0) {
          out = makearef(var, makeintc(s->offset), dot);
          if (s->basicdt == REAL) {
            out->basicdt = REAL;
            return out;
          }
          return out;
        }
        s = s->link;
      }

    }
	} else if (var->whichval == AREFOP) {
    int offset = var->operands->link->intval;
    s = var->operands->symtype->datatype;
    if (s->kind == RECORDSYM) {
      s = s->datatype;
      while(s) {
        if (strcmp(s->namestring, field->stringval) == 0) {
          var->operands->link->intval += s->offset;
          if (s->basicdt == REAL) var->basicdt = REAL;
          return var;
        }
        s = s->link;
      }
    }
    while (s) {
      if (offset == s->offset) {
        s = s->datatype->datatype->datatype;
        while (s) {
          if (strcmp(s->namestring, field->stringval) == 0) {
            var->operands->link->intval += s->offset;
            if(s->basicdt == REAL) {
              var->basicdt = REAL;
            }
            return var;
          }
          s = s->link;
        }
      }
      s = s->link;
    }
	} 
  s = searchst(var->stringval);
  s = s->datatype->datatype;
  while(s) {
        if (strcmp(s->namestring, field->stringval) == 0) {
          out = makearef(var, makeintc(s->offset), dot);
          if (s->basicdt == REAL) {
            out->basicdt = REAL;
            return out;
          }
          return out;
        }
        s = s->link;
      }
}

TOKEN makearef(TOKEN var, TOKEN off, TOKEN tok) {
  tok = makeop(AREFOP);
  tok->operands = var;
  var->link = off;
  return tok;
}


		
TOKEN dopoint(TOKEN var, TOKEN tok) {
  assert( var->symtype->kind == POINTERSYM);
  assert( var->symtype->datatype->kind == TYPESYM);
  tok->operands = var;
  SYMBOL s;
  // check if s is a pointer in the symbol table, make symentry point to  
  if ((s = searchst(var->stringval)) != NULL) {
    tok->symentry = s;
    tok->symtype = s->datatype->datatype->datatype;
  } else {
    // var is a pointer field in a record
    tok->symtype = var->operands->symtype;

  }
  return tok;
}

TOKEN arrayref2d (TOKEN aref, TOKEN next) {
  int innersize = aref->symtype->datatype->size;
  if(aref->symentry) {
    aref->operands->link->operands->intval += next->intval * innersize;
  } else {
    aref->operands->link->intval += next->intval * innersize;
  }
  aref->basicdt = aref->symtype->basicdt;
  aref->symtype = aref->symtype->datatype;
  return aref;
}

TOKEN arrayref(TOKEN arr, TOKEN tok, TOKEN subs, TOKEN tokb) {
  assert( arr->symtype->kind == ARRAYSYM );
  TOKEN out;
  SYMBOL s;
  SYMBOL ss;
  int elemsize = 0;
  s = arr->symtype;
  elemsize = s->datatype->size;
  if ((ss = searchst(subs->stringval)) != NULL) {
    TOKEN times_op = makeop(TIMESOP);
    TOKEN plus_op = makeop(PLUSOP);
    TOKEN neg = makeintc(-elemsize * s->lowbound);
    TOKEN size = makeintc(elemsize);
    TOKEN subscpy = copytok(subs);
    times_op = binop(times_op, size, subscpy);
    plus_op = binop(plus_op, neg, times_op);
    out = makearef(arr ,plus_op, tokb);
    out->symentry = s;
  } else {
    out = makearef(arr, makeintc(elemsize * (subs->intval - s->lowbound)) ,tokb);
  }
  out->basicdt = s->basicdt;
  out->symtype = s->datatype;
  if (subs->link) return arrayref2d(out, subs->link);
  return out;
}




  



TOKEN instfields(TOKEN idlist, TOKEN typetok) {
	int next = 0;
	int offset = 0;
	SYMBOL rec, typ;
	typ = searchst(typetok->stringval);
	TOKEN temp = idlist;
	while (temp) {
		rec = makesym(temp->stringval);
		rec->datatype = typ;
		offset = next;
		next = next + typ->size;
		rec->offset = offset;
		rec->datatype = typ;
    rec->size = typ->size;
		if (typ->kind == BASICTYPE) {
			rec->basicdt = typ->basicdt;
		}
		temp->symtype = rec;
		temp = temp->link;
	}
	return idlist;
}


TOKEN makesubrange(TOKEN tok, int low, int high) {
  TOKEN out = copytok(tok);
  SYMBOL range = symalloc();
  range->kind = SUBRANGE;
	range->basicdt = INTEGER;
	range->lowbound = low;
	range->highbound = high;
	range->size = basicsizes[INTEGER];
  out->symtype = range;
  return out;
}

TOKEN instrec(TOKEN rectok, TOKEN argstok) {
  int size, offset;
	SYMBOL rec = symalloc();
  rec->datatype = argstok->symtype;
	rec->kind = RECORDSYM;
	rectok->symtype = rec;
	offset = wordaddress(argstok->symtype->size, 8);
	size = offset;

	TOKEN curr = argstok;
	TOKEN next = argstok->link;
	while (next) {
		curr->symtype->link = next->symtype;
		offset = wordaddress(next->symtype->size, 8);		
		next->symtype->offset = size;
		size += offset;
		curr = next;
		next = next->link;
	}
  int remainder = size % 16;
  if (remainder != 0) {
    size += 16;
    size -= remainder;
  }
	rec->size = size;
	return rectok;
}


TOKEN findtype(TOKEN tok) {
  SYMBOL s, t;
  s = searchst(tok->stringval);
  t = s->datatype;
	if (s->kind == BASICTYPE) {
		tok->basicdt = s->basicdt;
		tok->symtype = s;
	} else {
		tok->symtype = t;
	}
	return tok;
}


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

TOKEN instarray(TOKEN bounds, TOKEN typetok) {
  if (bounds->link) {
    typetok = instarray(bounds->link, typetok);
    SYMBOL subrange = bounds->symtype;
    SYMBOL typesym = typetok->symtype;
    SYMBOL arraysym = symalloc();
    arraysym->kind = ARRAYSYM;
    arraysym->datatype = typesym;
    arraysym->lowbound = subrange->lowbound;
    arraysym->highbound = subrange->highbound;
    arraysym->size = (arraysym->highbound - arraysym->lowbound + 1) * (typesym->size);
    typetok->symtype = arraysym;
  return typetok;
  } else {
    SYMBOL subrange = bounds->symtype;
    SYMBOL typesym = typetok->symtype;
    SYMBOL arraysym = symalloc();
    arraysym->kind = ARRAYSYM;
    arraysym->datatype = typesym;
    arraysym->lowbound = subrange->lowbound;
    arraysym->highbound = subrange->highbound;
    arraysym->size = (arraysym->highbound - arraysym->lowbound +  1) * (typesym->size);
    typetok->symtype = arraysym;
    return typetok;
  }
}

TOKEN nconc(TOKEN lista, TOKEN listb) {
  TOKEN temp = lista;
  while (temp->link) {
    temp = temp->link;
  }
  temp->link = listb;
  return lista;
}


TOKEN instenum(TOKEN idlist) {
  int size = 0;
    TOKEN temp = idlist;
    while (temp) {
      instconst(temp, makeintc(size));
      size++;
      temp = temp->link;
    }
    return makesubrange(idlist, 0 ,size - 1);
}

TOKEN makewhile(TOKEN tok, TOKEN expr, TOKEN tokb, TOKEN statement) {
	TOKEN lab = makelabel();
  TOKEN progl = makeprogn(tok, lab);
  TOKEN iftok = makeif(talloc(), expr, statement, NULL);
  lab->link = iftok;
  TOKEN gt;
  gt = statement->operands;
  while(gt->link) {
    gt = gt->link;
  }
  gt->link = makegoto(labelnumber - 1);
  return progl;
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
         printf("lhs basicdt: %d, rhs basicdt: %d\n", lhs->basicdt, rhs->basicdt);
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

  if (strcmp(fn->stringval, "new") == 0) {
    tok = makeop(ASSIGNOP);
    tok->operands = args;
    TOKEN func = makeop(FUNCALLOP);
    args->link = func;
    func->operands = fn;
    fn->link = makeintc(searchst(args->stringval)->datatype->datatype->datatype->size);
    return tok;
  }
  if (strcmp(fn->stringval, "write") == 0) {
    if (args->basicdt == INTEGER) {
      strcpy(fn->stringval, "writei");
    }
    if (args->basicdt == REAL) {
      strcpy(fn->stringval, "writef");
    }
  }
  if (strcmp(fn->stringval, "writeln") == 0) {
    if (args->basicdt == INTEGER) {
      strcpy(fn->stringval, "writelni");
    }
    if (args->basicdt == REAL) {
      strcpy(fn->stringval, "writelnf");
    }
  }

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
  out->basicdt = origtok->basicdt;
  out->symtype = origtok->symtype;
  out->symentry = origtok->symentry;
  out->operands = origtok->operands;
  out->link = origtok->link;
  if (origtok->whichval != -1) {
    out->whichval = origtok->whichval;
  } else if (origtok->stringval[0] != '\0') {
		strcpy(out->stringval, origtok->stringval);
	} else if (origtok->realval != -DBL_MIN) {
		out->realval = origtok->realval;
	} else {
		out->intval = origtok->intval;
	}
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

void  instlabel (TOKEN num) {
  labels[labelnumber] = num->intval;
  labelnumber++;
}

void instvars(TOKEN idlist, TOKEN typetok)
  { SYMBOL sym, typesym; int align;
    typesym = typetok->symtype;
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

        // todo this part is not running
        if (typesym->datatype != NULL && typesym->datatype->kind == ARRAYSYM) {
			      SYMBOL arr = typesym->datatype;
			        while (arr && arr->kind == ARRAYSYM) {
				        arr = arr->datatype;
			        }
			      if (arr->kind == BASICTYPE) {
				      sym->basicdt = arr  ->basicdt;
			}
		}
        idlist = idlist->link;
  }
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

void  insttype(TOKEN typename, TOKEN typetok) {
   SYMBOL t = searchins(typename->stringval);
   t->kind = TYPESYM;
   t->size = typetok->symtype->size;
   t->datatype = typetok->symtype;
}


int main(void)          /*  */
  { int res;
    initsyms();
    res = yyparse();
    printstlevel(1);       /* to shorten, change to:  printstlevel(1);  */
    printf("yyparse result = %8d\n", res);
    if (DEBUG & DB_PARSERES) dbugprinttok(parseresult);
    ppexpr(parseresult);           /* Pretty-print the result tree */
    /* uncomment following to call code generator. */
     /* 
    gencode(parseresult, blockoffs[blocknumber], labelnumber);
 */
  }