/* lex1.c         14 Feb 01; 31 May 12; 11 Jan 18       */

/* This file contains code stubs for the lexical analyzer.
   Rename this file to be lexanc.c and fill in the stubs.    */

/* Copyright (c) 2018 Gordon S. Novak Jr. and
   The University of Texas at Austin. */

/*
    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include <assert.h>
#include "token.h"
#include "lexan.h"

#define MAXINT 2147483647

char* reserveds[29] = 
{"array", "begin", "case", "const", "do", "downto", "else", "end", "file", "for",
"function", "goto", "if", "label", "nil", "of", "packed", "procedure", "program",
"record", "repeat", "set", "then", "to", "type", "until", "var", "while", "with"}; 

char* opwords[] = {"and", "or", "not", "div", "mod", "in"};

char* ops[] = {"+", "-", "*", "/", ":=", "=", "<>", "<", "<=", ">=", ">",  "^", "."};
char* delim[] = {",", ";", ":", "(", ")", "[", "]", ".."};


/* This file will work as given with an input file consisting only
   of integers separated by blanks:
   make lex1
   lex1
   12345 123    345  357
   */

int t = 0;
double tens[23];                           /* powers of ten*/

void init_tens() {
  tens[0] = 1.0;
  for (int i = 1; i < 23; i++) {
    tens[i] = 10 * tens[i-1];
  }
  t = 1;
}


/* Skip blanks and whitespace.  Expand this function to skip comments too. */
void skipblanks ()
  {
      if (t) goto skip;
      init_tens();
      skip:
      t = 1;
      int c, cc;
      while ((c = peekchar()) != EOF
             && (c == ' ' || c == '\n' || c == '\t' || c == '{' || c == '('))
          if (c == '(') {
            if (peek2char() == '*') {
              getchar();
              getchar();
              c = peekchar();
              cc = peek2char();
              while (c != '*' || cc != ')') {
                getchar();
                c = peekchar();
                cc = peek2char();
              }
              assert (c == '*' && cc == ')');
              getchar();
              getchar();
            } else return;
          } else if (c == '{') {
            while ((c = peekchar()) != '}') {
              getchar();
            }
            assert (c == '}');
            getchar();
          }
          else {  
            getchar();
          }
    }

/* Get identifiers and reserved words */
TOKEN identifier (TOKEN tok)
  {
    int i = 0;
    int c;
    tok->tokentype = IDENTIFIERTOK;
    while (CHARCLASS[c = peekchar()] == ALPHA || CHARCLASS[c] == NUMERIC) {
      if (i < 15) {
        tok->stringval[i] = (char) getchar();
        i++;
      } else {
        c = getchar();
      }
    }
    if (i < 15) tok->stringval[i + 1] = '\0';
    else tok->stringval[15] = '\0';
    for (i = 0; i < 29; i++) {
      if (strcmp(reserveds[i], tok->stringval) == 0) {
        tok->whichval = 1 + i;
        tok->tokentype = RESERVED;
        return tok;
      }
    }
    for (i = 0; i < 6; i++) {
      if (strcmp(opwords[i], tok->stringval) == 0) {
        tok->tokentype = OPERATOR;
        switch (i)
        {
        case 0:
          tok->whichval = ANDOP;
          break;
        case 1:
          tok->whichval = OROP;
          break;
         case 2:
          tok->whichval = NOTOP;
         case 3:
          tok->whichval = DIVOP;
          break; 
        case 4:
          tok->whichval = MODOP;
          break;
        case 5:
          tok->whichval = INOP;
          break;
        default:
          break;     
        }
      }
    }
    return tok;
  }

TOKEN getstring (TOKEN tok)
  {
    tok->tokentype = STRINGTOK;
    assert(peekchar() == '\'');
    getchar();
    int i = 0;
    int c;
    int done = 0;
    while (i < 15 && peekchar() != '\'') {
      tok->stringval[i] = getchar();
      c = peekchar();
      if (peek2char() == '\'' && c == '\'') {
        getchar();
        i++;
        if (i < 15) tok->stringval[i] = '\'';
        getchar();
      }
      i++;
    }
    while (peekchar() != '\'') getchar();
    assert(peekchar() == '\'');
    getchar();
    return tok;
  }

TOKEN special (TOKEN tok)
  {
    int c = getchar();
    int cc = peekchar();
    // todo fix reserved words that are operators

    if (c == '+') {
        tok->tokentype = OPERATOR;
        tok->whichval = PLUSOP;
    } else if (c == '-') {
        tok->tokentype = OPERATOR;
        tok->whichval = MINUSOP;
    } else if (c == '*') {
        tok->tokentype = OPERATOR;
        tok->whichval = TIMESOP;
    } else if (c == '/') {
        tok->tokentype = OPERATOR;
        tok->whichval = DIVIDEOP;
    } else if (c == ':') {
        if (cc == '=') {
          tok->tokentype = OPERATOR;
          tok->whichval = ASSIGNOP;
          getchar();
        } else {
          tok->tokentype = DELIMITER;
          tok->whichval = COLON - DELIMITER_BIAS;
        }
    } else if (c == '=') {
        tok->tokentype = OPERATOR;
        tok->whichval = EQOP;
    } else if (c == '<') {
        tok->tokentype = OPERATOR;
        if (cc == '>') {
          tok->whichval = NE;
          getchar();
        }
        else if (cc == '=') {
          tok->whichval = LE;
          getchar();
        }
        else tok->whichval = LT;
    } else if (c == '>') {
        tok->tokentype = OPERATOR;
        if (cc == '=') {
          tok->whichval = GE;
          getchar();
        }
        else tok->whichval = GT;
    } else if (c == '^') {
        tok->tokentype = OPERATOR;
        tok->whichval = POINT;      
    } else if (c == '.') {       
        if (cc == '.') {
          tok->tokentype = DELIMITER;
          tok->whichval = DOTDOT - DELIMITER_BIAS;
          getchar();
        } else {
          tok->tokentype = OPERATOR;
          tok->whichval = DOTOP;  
        }    
    } else if (c == ',') {
        tok->tokentype = DELIMITER;
        tok->whichval = COMMA - DELIMITER_BIAS;              
    } else if (c == ';') {
        tok->tokentype = DELIMITER;
        tok->whichval = SEMICOLON - DELIMITER_BIAS;
    } else if (c == '(') {
        tok->tokentype = DELIMITER;
        tok->whichval = LPAREN - DELIMITER_BIAS;
    } else if (c == ')') {        
        tok->tokentype = DELIMITER;
        tok->whichval = RPAREN - DELIMITER_BIAS;
    } else if (c == '[') {
        tok->tokentype = DELIMITER;
        tok->whichval = LBRACKET - DELIMITER_BIAS;
    } else if (c == ']') {
        tok->tokentype = DELIMITER;
        tok->whichval = RBRACKET - DELIMITER_BIAS;
    }
    return tok;
  }
    

// returns number of consecutive zeroes
  int countzeroes() {
    int c;
    int i = 0;
    while  (peekchar() == '0') {
      getchar();
      i++;
    }
    return i;
  }

  // if f is below zero there is no decimal parsed yet
  int expon() {
    int c = peekchar();
    int sign = 1;
    if (c != 'e') return 0;
    if (c == 'e') getchar();
    if ((c = peekchar()) == '+') getchar();
    else if(c == '-') {
      getchar();
      sign = -1;
    }
    int charval;
    int exp = 0;
    countzeroes();
    while ((c = peekchar()) != EOF && CHARCLASS[c] == NUMERIC) {
      c = getchar();
      charval = c - '0';
      exp = exp * 10 + charval;
    }
    if (sign == -1) exp *= -1;
    return exp;
  }

  // [0] is num [1] is number of decimal digits
  // [2] is overflow. n[3] is the leading zeroes in front of the decimal
  decimal(long * n) {
    assert(peekchar() == '.');
    getchar();
    if (n[0] == 0) {
      n[3] = countzeroes();
    }
    n[1] += n[3] + 1;
    int c, charval;
    if (n[0] && !n[2]) {
      for (int i = 0; i < n[1]; i++) {
        if (n[0] > MAXINT / 10) {
          n[2] = 1;
          break;
        }
        n[0] *= 10;
      }
    }
    while ((c = peekchar()) != EOF && CHARCLASS[c] == NUMERIC) {
      c = getchar();
      charval = c - '0';
      if (n[0] > MAXINT / 10 || (n[0] == MAXINT / 10 && charval > 7)) n[2] = 1;
      if (!n[2]) n[0] = n[0] * 10 + charval;
      else break;
      n[1]++;
    }
    while ((c = peekchar()) != EOF && CHARCLASS[c] == NUMERIC) getchar();
  }



  TOKEN number (TOKEN tok) {
    tok->tokentype = NUMBERTOK;
    double fnum = 0;
    int c, charval;
    int digsb4dec = 0; //digits before decimal excluding leading zeroes
    int overflow = 0;
    int exp = 0;
    long nums[4] = {0, -1, 0, 0}; // nums[0] is number, nums[1] is digits after the decimal point
    // nums [2] is overflow, nums[3] is number of leading zeroes after the decimal if number is less than 1
    countzeroes();
    if (peekchar() == '.' && CHARCLASS[peek2char()] == NUMERIC) {
      decimal(nums);
      goto epart;
    }
    while ((c = peekchar()) != EOF && CHARCLASS[c] == NUMERIC) {
      c = getchar();
      charval = c - '0';
      digsb4dec++;
      if (nums[0] > MAXINT / 10 || (nums[0] == MAXINT / 10 && charval > 7)) nums[2] = 1;
      if (!nums[2]) nums[0] = nums[0] * 10 + charval;
      if (peekchar() == '.' && CHARCLASS[peek2char()] == NUMERIC) {
        decimal(nums);
      }
    }
    epart:
      exp = expon();
      if (exp == 0 && nums[1] == -1) { // integer, no exponent part or decimal parts
        tok->basicdt = INTEGER;
        tok->intval = nums[0];
        if (nums[2]) printf("Integer number out of range\n");
        return tok;
      } else {
        tok->basicdt = REAL;
        // make the number 9 digits
        while (nums[0] < tens[8]) {
          nums[0] *= 10;
        } 
        if (nums[0] >= tens[9]) nums[0] = nums[0] / 10;
        fnum = (double) nums[0];
        if (digsb4dec == 0) {// number part is less than 1
          exp = exp - nums[3] - 9; // exp is equal to the exponent part minus the number leading zeroes
                              // minus 1. the extra 1 is because the number part is less than 1.
        } else {
          // whole number part 10 or more digits
          exp = exp + digsb4dec - 9;
        }
        if (exp + 9 > 38 || exp + 9 < -38) printf("Floating number out of range\n");
        if (exp < 0) {
          exp *= -1;
          while (exp > 22) {
            fnum = fnum / tens[22];
            exp -= 22;
          }
          tok->realval = fnum / tens[exp];
        } else {
          while (exp > 22) {
            fnum = fnum * tens[22];
            exp -= 22;
          }
          tok->realval = fnum * tens[exp];
        }
      }
    return tok;
  }





  







  


