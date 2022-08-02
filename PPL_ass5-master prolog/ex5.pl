/*
 * **********************************************
 * Printing result depth
 *
 * You can enlarge it, if needed.
 * **********************************************
 */
maximum_printing_depth(100).

:- current_prolog_flag(toplevel_print_options, A),
   (select(max_depth(_), A, B), ! ; A = B),
   maximum_printing_depth(MPD),
   set_prolog_flag(toplevel_print_options, [max_depth(MPD)|B]).

% Signature: unique(List, UniqueList, Dups)/3
% Purpose: succeeds if and only if UniqueList contains the same elements of List without duplicates (according to their order in List), and Dups contains the duplicates

list(empty).
list(cons(X,Xs)):-list(Xs).
member(X,[X|_Xs]).
member(X,[Y|Ys]):-member(X,Ys).
append([],Xs,Xs).
append([X | Xs], Ys,[X | Zs]):- append(Xs,Ys,Zs).

notmember(X,[]).
notmember(X,[Y | Ys]):- X\=Y,notmember(X,Ys).

delMember(_, [], []).
delMember(X, [X|Xs], Y) :-
    delMember(X, Xs, Y).
delMember(X, [T|Xs], [T|Y]) :-
    X\=T,
    delMember(X, Xs, Y).


unique([],[],[]).

unique([X | Xs], [X | Ys], Zs):-
    notmember(X, Xs),
    delMember(X, Xs, L),
    unique(L,Ys,Zs).

unique([X | Xs], [X | Ys], [X | Zs]):-
    member(X,Xs),
    delMember(X,Xs,L),
    unique(L,Ys,Zs).
            
            



            
                        