% descmutants.pl -- describe mutants of input file
% Copyright (c) 2005 Jamie Andrews (andrews [[at]] csd.uwo.ca)
%
% This program is free software; you can redistribute it and/or modify
% it under the terms of the GNU General Public License as published by
% the Free Software Foundation; either version 2 of the License, or
% (at your option) any later version.
%
% This program is distributed in the hope that it will be useful,
% but WITHOUT ANY WARRANTY; without even the implied warranty of
% MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
% GNU General Public License for more details.
%
% You should have received a copy of the GNU General Public License
% along with this program; if not, write to the Free Software
% Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307, USA.
%
% Changes:
%   None (first public release).

describe_mutants :-
  prompt(_, ' '),
  read_line(Line),
  dm_rest(Line, 1, no, yes),
  halt.

% dm_rest(Line, Lineno, Incomment, Beginstmt):  describe mutants
% in rest of file, given that current line is Line and line number
% of current line is Lineno; Incomment (yes or no) indicates
% whether we are in a comment at the beginning of the line;
% and Beginstmt indicates whether we think that the first non-comment
% text on this line begins a statement.
dm_rest(end_of_file, _, _, _) :- !.
dm_rest(Line, Lineno, Incomment, Beginstmt) :-
  dm_line(Line, Lineno, Incomment, Beginstmt),
  status_at_end(Line, Incomment, Beginstmt, Incomment_end, Beginstmt_end),
  read_line(Newline),
  Lineno1 is Lineno+1,
  dm_rest(Newline, Lineno1, Incomment_end, Beginstmt_end).

% failure driven loop
dm_line(Line, Lineno, Incomment, Beginstmt) :-
  mutant(Line, Incomment, Beginstmt, Mutant),
  display_mutant(Lineno, Mutant),
  fail.
dm_line(_, _, _, _).

mutant(Line, Incomment, Beginstmt, Mutant) :-
  to_end_of_comment(Line, Incomment, TEOC, Rest),
  to_beginning_of_comment_or_end(Rest, TBOCOE, Rest2),
  base_mutant(TBOCOE, Beginstmt, BaseMutant),
  append(TEOC, BaseMutant, First2),
  append(First2, Rest2, Mutant).

to_end_of_comment(Line, no, [], Line).
to_end_of_comment(Line, yes, "*/", Rest) :-
  append("*/", Rest, Line),
  !.
to_end_of_comment([C|Cs], yes, [C|TEOC], Rest) :-
  to_end_of_comment(Cs, yes, TEOC, Rest).

to_beginning_of_comment_or_end([], [], []).
to_beginning_of_comment_or_end(Line, [], Line) :-
  append("//", _, Line),
  !.
to_beginning_of_comment_or_end(Line, [], Line) :-
  append("/*", _, Line),
  !.
to_beginning_of_comment_or_end([C|Cs], [C|TBOCOE], Rest) :-
  to_beginning_of_comment_or_end(Cs, TBOCOE, Rest).

base_mutant(Line, Beginstmt, Mutant) :-
  append("#", _, Line),
  !,
  bb_mutant(Line, Beginstmt, BBMutant, "rep_const"),
  append(BBMutant, " /* MUTANT (rep_const) */", Mutant).
base_mutant(Line, Beginstmt, Mutant) :-
  bb_mutant(Line, Beginstmt, BBMutant, Operator),
  append("/* MUTANT (", X1, Mutant),
  append(Operator, X2, X1),
  append(") */", X3, X2),
  X3 = BBMutant.

% base base mutant
bb_mutant(Text, yes, Mutant, "del_stmt") :-
  delete_1ormore_statements(Text, no, Mutant).
bb_mutant(Text, _, Mutant, "rep_op") :-
  replace_1ormore_operators(Text, no, Mutant).
bb_mutant(Text, _, Mutant, "rep_const") :-
  replace_1ormore_constants(Text, no, no, Mutant).
bb_mutant(Text, _, Mutant, "negate") :-
  negate_first_decision(Text, no, Mutant).

display_mutant(Lineno, Mutant) :-
  name(Lineno, LinenoString),
  append(LinenoString, ": ", String2),
  append(String2, Mutant, String3),
  writestring(String3), nl.

status_at_end([], Incomment, Beginstmt, Incomment, Beginstmt).
% if right now in comment (2 clauses)
status_at_end(Line, yes, Beginstmt, Incomment_end, Beginstmt_end) :-
  append("*/", Rest, Line),
  !,
  status_at_end(Rest, no, Beginstmt, Incomment_end, Beginstmt_end).
status_at_end([_|Cs], yes, Beginstmt, Incomment_end, Beginstmt_end) :-
  status_at_end(Cs, yes, Beginstmt, Incomment_end, Beginstmt_end).
% if not right now in comment
% beginning new comment
status_at_end(Line, no, Beginstmt, Incomment_end, Beginstmt_end) :-
  append("/*", Rest, Line),
  !,
  status_at_end(Rest, yes, Beginstmt, Incomment_end, Beginstmt_end).
% beginning comment to end-of-line
status_at_end(Line, no, Beginstmt, no, Beginstmt) :-
  append("//", _, Line),
  !.
status_at_end([C|Cs], no, Beginstmt, Incomment_end, Beginstmt_end) :-
  char_type(C, space),
  !,
  status_at_end(Cs, no, Beginstmt, Incomment_end, Beginstmt_end).
% "{":  regardless of whether in stmt or not, now at beginning of stmt
status_at_end(Line, no, _, Incomment_end, Beginstmt_end) :-
  append("{", Rest, Line),
  !,
  status_at_end(Rest, no, yes, Incomment_end, Beginstmt_end).
% ";":  similar
status_at_end(Line, no, _, Incomment_end, Beginstmt_end) :-
  append(";", Rest, Line),
  !,
  status_at_end(Rest, no, yes, Incomment_end, Beginstmt_end).
% going into a statement -- nonblank, non-{
status_at_end([_|Cs], no, _, Incomment_end, Beginstmt_end) :-
  status_at_end(Cs, no, no, Incomment_end, Beginstmt_end).

all_blanks([]).
all_blanks(Line) :-
  append(" ", Rest, Line),
  all_blanks(Rest).

%%% Mutant predicates

% delete_1ormore_statements(Text, Sofar, Mutant): generate Mutant
% from Text by deleting one or more statements, given that Sofar
% indicates whether we already have deleted at least one.
delete_1ormore_statements(Text, _Sofar, Mutant) :-
  append(First_stmt, SemiRest, Text),
  append(";", Rest, SemiRest),
  poss_balanced_pars(First_stmt, Afterpars),
  all_blanks(Afterpars),
  !,
  ( ( delete_0ormore_statements(Rest, Mutant1),
      append_multi([" /* ", First_stmt, "; */ ", Mutant1], Mutant)
      % , writestring(First_stmt), nl
    )
  ; ( delete_1ormore_statements(Rest, _, Mutant1),
      append_multi([First_stmt, ";", Mutant1], Mutant)
    )
  ).
delete_0ormore_statements(Text, Text).
delete_0ormore_statements(Text, Mutant) :-
  delete_1ormore_statements(Text, _, Mutant).

replace_1ormore_operators([], yes, []).
replace_1ormore_operators(Text, Sofar, Mutant) :-
  Sofar=no,
  operator_at_beginning(Operator, Rest, Text, no),
  !,
  ( ( operator_class(Operator, Class, yes),
      operator_class(Replacement, Class, _),
      Replacement \= Operator,
      replace_1ormore_operators(Rest, yes, Mutant1),
      append(Replacement, Mutant1, Mutant)
    )
  ; ( replace_1ormore_operators(Rest, Sofar, Mutant1),
      append(Operator, Mutant1, Mutant)
    )
  ).
replace_1ormore_operators(Text, Sofar, Mutant) :-
  Sofar=no,
  append("""", Rest1, Text),
  !,
  append(Stringcontents, ClosequoteRest2, Rest1),
  append("""", Rest2, ClosequoteRest2),
  replace_1ormore_operators(Rest2, Sofar, Mutant2),
  append_multi(["""", Stringcontents, """", Mutant2], Mutant).
replace_1ormore_operators([C|Text], Sofar, [C|Mutant]) :-
  replace_1ormore_operators(Text, Sofar, Mutant).

replace_1ormore_constants([], _, yes, []).
replace_1ormore_constants(Text, InIdent, Sofar, Mutant) :-
  Sofar=no,
  InIdent=no,
  constant_at_beginning(Constant, Rest, Text, no),
  !,
  ( ( (typical_constant(Replacement) ; derived_constant(Constant, Replacement)),
      Replacement \= Constant,
      replace_1ormore_constants(Rest, no, yes, Mutant1),
      append(Replacement, Mutant1, Mutant)
    )
  ; ( replace_1ormore_constants(Rest, Sofar, no, Mutant1),
      append(Constant, Mutant1, Mutant)
    )
  ).
replace_1ormore_constants([C|Text], _, Sofar, [C|Mutant]) :-
  char_type(C, csym),  % letter, digit or _
  !,
  replace_1ormore_constants(Text, yes, Sofar, Mutant).
replace_1ormore_constants([C|Text], _, Sofar, [C|Mutant]) :-
  replace_1ormore_constants(Text, no, Sofar, Mutant).

negate_first_decision(Text, _, Mutant) :-
  decision(Text, Keyword, Decision, Rest),
  !,
  append_multi([Keyword,"(!",Decision,")",Rest], Mutant).
negate_first_decision([C|Text], _, [C|Mutant]) :-
  negate_first_decision(Text, _, Mutant).

%%% Mutant predicate utilities

operator_at_beginning([X|Xs], Y, [X|Zs], _) :-
  member(X, "+-*%&|<=>!"),
  !,
  operator_at_beginning(Xs, Y, Zs, yes).
operator_at_beginning([], Rest, Rest, yes).

%operators(Os) :-.
%  bagof(O, Class^operator_class(O, Class), Os).

operator_class("+", arith, yes).
operator_class("-", arith, no).   % could be unary
operator_class("*", arith, no).   % looks like a dereferencing star
operator_class("%", arith, yes).
operator_class("&&", logical, yes).
operator_class("||", logical, yes).
operator_class("&", bitmask, no).  % looks like address-taking ampersand
operator_class("|", bitmask, yes).
operator_class("++", prepost, yes).
operator_class("--", prepost, yes).
operator_class("<=", comp, yes).
operator_class("<",  comp, yes).
operator_class(">",  comp, yes).
operator_class(">=", comp, yes).
operator_class("==", comp, no).     % ie. not replaceable by <, > etc....
operator_class("!=", comp, no).     % ...but able to replace them...
operator_class("==", eqcomp, yes).  % ...and replaceable by each other
operator_class("!=", eqcomp, yes).
operator_class("+=", arithasmt, yes).
operator_class("-=", arithasmt, yes).
operator_class("*=", arithasmt, yes).
operator_class("%=", arithasmt, yes).

constant_at_beginning([X|Xs], Y, [X|Zs], Sofar) :-
  [X] = "-",
  !,
  cab1(Xs, Y, Zs, Sofar).
constant_at_beginning(X, Y, Z, Sofar) :-
  cab1(X, Y, Z, Sofar).
cab1([X|Xs], Y, [X|Zs], _) :-
  char_type(X, digit),
  % member(X, "0123456789"),
  !,
  cab1(Xs, Y, Zs, yes).
cab1([], Rest, Rest, yes) :-
  % Just don't want real constants
  \+ append(".", _, Rest).

typical_constant("0").
typical_constant("1").
typical_constant("-1").
%typical_constant("32767").
%typical_constant("-32768").

derived_constant(Constant, Replacement) :-
  (\+ (Constant = "0")),   % will be repl by 1 already
  append("((", Constant, Constant1),
  append(Constant1, ")+1)", Replacement).
derived_constant(Constant, Replacement) :-
  (\+ (Constant = "0")),   % will be repl by -1 already
  (\+ (Constant = "1")),   % will be repl by 0 already
  append("((", Constant, Constant1),
  append(Constant1, ")-1)", Replacement).

decision(Text, Keyword, Decision, Rest) :-
  ( ( append("if", Text1, Text),
      Keyword = "if"
    )
  ; ( append("while", Text1, Text),
      Keyword = "while"
    )
  ),
  balanced_pars(Text1, Rest),
  append(Decision, Rest, Text1).

balanced_pars -->
  "(",
  {!},
  until_endpar(1),
  poss_balanced_pars.
balanced_pars -->
  [_],
  balanced_pars.

poss_balanced_pars --> [].
poss_balanced_pars -->
  "(",
  {!},
  until_endpar(1),
  poss_balanced_pars.
poss_balanced_pars -->
  [_],
  poss_balanced_pars.

until_endpar(Nesting) -->
  "(",
  {!, Nesting1 is Nesting+1},
  until_endpar(Nesting1).
until_endpar(1) -->
  ")",
  {!}.
until_endpar(Nesting) -->
  ")",
  {!, Nesting1 is Nesting-1},
  until_endpar(Nesting1).
until_endpar(Nesting) -->
  [_],
  until_endpar(Nesting).

append_multi([], []).
append_multi([L|Ls], Z) :-
  append(L, Y, Z),
  append_multi(Ls, Y).

%% usual utils

read_line(String) :-
  get0(Char),
  ( Char = -1 ->
    String = end_of_file;
    Char = 10 ->
    String = [];
    ( String = [Char|Chars],
      read_line(Chars)
    )
  ).

writestring([]).
writestring([C|Cs]) :-
  put(C),
  writestring(Cs).

