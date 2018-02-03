:- module(rozwiazanie, [resolve/4, prove/2]).

% definiujemy operatory ~/1 oraz v/2
:- op(200, fx, ~).
:- op(500, xfy, v).

% sprawdza, czy X jest literalem
literal(X) :- 
	atom(X).
literal(~X) :- 
	atom(X).

% spelnione, jesli literal X jest odpowiednio pozytywny lub negatywny
pozytywny(X) :- atom(X).
negatywny(~X) :- atom(X).

% znajduje postac zanegowanego literalu 
negacja(~X,X) :- !.
negacja(X,~X).

% "wartosc absolutna" ze zmiennej
zmienna(L,L) :-
	literal(L),
	pozytywny(L), !.
zmienna(L,N) :-
	negacja(L,N).

% zwraca posortowana liste list wzgledem ich dlugosci
sortujPoDlugosci([],[]).
sortujPoDlugosci([G|O],[G|W]) :-
	length(G,DG),
	forall(member(E,O),(length(E,DE),DG =< DE)),
	sortujPoDlugosci(O,W), !.
sortujPoDlugosci([A,B|O],W) :-
	append(O,[A],C),
	sortujPoDlugosci([B|C],W).

%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%% KONWERSJE %%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%

% zwraca liste literalow w klauzuli
% a v b => [a,b]
zamianaKlauzulaNaListe(L,[L]) :- 
	literal(L).
zamianaKlauzulaNaListe(L v K,[L|O]) :-
	zamianaKlauzulaNaListe(K,O).

% bierze liste literalow, zwraca ich alternatywe
% [[a,b],[c]] => a v b, c
zamianaListaNaKlauzule([],[]).
zamianaListaNaKlauzule([H],H) :- !.
zamianaListaNaKlauzule([H|T],H v Y) :- 
	literal(H), 
	zamianaListaNaKlauzule(T,Y).

% zwraca klauzule na podstawie jej rodowodu
% (rez(rez(axiom(p),axiom(~p v r),r),axiom(~r v t),t) => t
zamianaDrzewoNaKlauzule(axiom(X),Y) :- 
	zamianaDrzewoNaKlauzule(X,Y), !.
zamianaDrzewoNaKlauzule(rez(_,_,_,rez(_,_,_,X)),Y) :- 
	zamianaDrzewoNaKlauzule(X,Y), !.
zamianaDrzewoNaKlauzule(rez(_,_,_,X),Y) :- 
	zamianaDrzewoNaKlauzule(X,Y), !.

zamianaDrzewoNaKlauzule(axiom(X),X) :- !.
zamianaDrzewoNaKlauzule(rez(_,_,_,X),X) :- !.

% zwraca zbior wszystkich literalow w klauzuli - liste bez powtorzen
% a v b v b => [a,b]
zbiorLiteralow(K,W) :- 
	zamianaKlauzulaNaListe(K,L), 
	sort(L,W). 

% zamienia wszystkie klauzule na listy literalow, zwraca liste tych list 
% [a v b v b, c v d] => [[a, b], [c, d]]
listaList(L,W) :-
	listaList(L,[],R),
	reverse(R,W).

	listaList([],W,W).
	listaList([G|O],A,W) :-
		zbiorLiteralow(G,L), 
		append([L],A,A2),
		listaList(O,A2,W).

% zamienia wszystkie listy na klauzule, zwraca liste tych klauzul
% [[a, b], [c, d]] => [a v b v b, c v d] 
listaKlauzul(L,W) :-
	listaKlauzul(L,[],R),
	reverse(R,W).

	listaKlauzul([],W,W).
	listaKlauzul([G|O],A,W) :-
		zamianaListaNaKlauzule(G,L), 
		append([L],A,A2),
		listaKlauzul(O,A2,W).

% wyciaga klauzule z listy ich rodowodow
% [axiom(p v w),axiom(p),rez(axiom(p),axiom(q),z)] => [p v w, p, z].

listaDrzew(L,W) :-
	listaDrzew(L,[],R),
	reverse(R,W).

	listaDrzew([],W,W).
	listaDrzew([G|O],A,W) :-
		zamianaDrzewoNaKlauzule(G,L), 
		append([L],A,A2),
		listaDrzew(O,A2,W).

% wyciaga klauzule z listy list ich rodowodow
% [[rez(rez(axiom(p v q), axiom(~p v q), p, q), rez(axiom(p v ~q), axiom(~p v ~q), p, ~q), q, [])], [rez(axiom(p v q), axiom(~p v q), p, q), rez(axiom(p v ~q), axiom(~p v ~q), p, ~q)], [axiom(p v q), axiom(~p v q), axiom(p v ~q), axiom(~p v ~q)]] => [[], ~q, q, ~p v ~q, p v ~q, ~p v q, p v q]
listaListDrzew(L,W) :-
	listaListDrzew(L,[],R),
	reverse(R,W).

	listaListDrzew([],W,W).
	listaListDrzew([G|O],A,W) :-
		listaDrzew(G,L),
		append(L,A,A2),
		listaListDrzew(O,A2,W).

%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%% ZMIENNE ZDANIOWE %%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%

% pobiera liste unikalnych literalow, jesli w liscie wystepuje literal 
% pozytywny i negatywny tej samej zmiennej zdaniowej, to na liscie 
% wynikowej pozostaje tylko literal negatywny
unikatowe([],[]).
unikatowe([G|O],[G|W]) :-
	negacja(G,NG),
	\+ member(NG,O), !,
	unikatowe(O,W).
unikatowe([G|O],W) :-
	negacja(G,NG),
	member(NG,O), !,
	unikatowe(O,W).

% zamienia negatywne wystapienia literalu na pozytywne
samePozytywne(L,W) :- 
	samePozytywne(L,[],W).

	samePozytywne([],A,A).
	samePozytywne([G|O],A,W) :-
		literal(G),
		zmienna(G,Z),
		A2 = [Z|A],
		samePozytywne(O,A2,W).

% zwraca liste unikalnych zmiennych zdaniowych
zmienneZdaniowe(L,W) :- 
	listaList(L,LK),
	sort(LK,LK2),
	flatten(LK2,F),
	sort(F,FS),
	unikatowe(FS,U),
	sort(U,US),
	samePozytywne(US,W).

%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%% REZOLWENTA %%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%

% zwraca rezolwente w postaci listy
rezolwenta(Z,KP,KN,W) :-
	literal(Z), 
	negacja(Z,ZN), 
	select(Z,KP,KP2), !,
	select(ZN,KN,KN2), !,
	append(KP2,KN2,R),
	sort(R,W).

% zwraca rezolwente w postaci klauzuli
resolve(Z,KP,KN,W) :-
	zbiorLiteralow(KP,LP),
	zbiorLiteralow(KN,LN),
	rezolwenta(Z,LP,LN,R),
	zamianaListaNaKlauzule(R,W).

%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%% REZOLUCJA %%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%

% nadanie idekow klazulom "pierwotnym"
axiomId(L,W) :-
	axiomId(L,[],R),
	reverse(R,W).

	axiomId([],A,A).
	axiomId([G|O],A,W) :-
		N = axiom(G),
		A2 = [N|A],
		axiomId(O,A2,W).

% zwraca liste klauzul z wystapieniem literalu
%?- znajdzKlauzule([axiom(p v w),axiom(p),rez(axiom(p),axiom(q),z)],p,X).
%X = [axiom(p), axiom(p v w)].
znajdzKlauzule(Z,L,W) :-
	literal(L),
	listaDrzew(Z,D),
	listaList(D,LK),
	znajdzKlauzule(LK,Z,L,[],W).

	znajdzKlauzule([],[],_,A,A).
	znajdzKlauzule([G|O],[H|T],L,A,W) :-
		member(L,G), !,
		append([H],A,A2),
		znajdzKlauzule(O,T,L,A2,W).
	znajdzKlauzule([G|O],[_|T],L,A,W) :-
		\+ member(L,G), !,
		znajdzKlauzule(O,T,L,A,W).

% sprawdza, czy wystapila klauzula pusta w dowodzie
sprzecznosc(D) :-
	listaDrzew(D,LD),
	member([],LD).

% sprawdza, czy nie wystepuje p v ~p q klauzuli
bezTautologii([]).
bezTautologii(R) :-
	zbiorLiteralow(R,Z),
	bezTautologiiPom(Z).

	bezTautologiiPom([]).
	bezTautologiiPom([G|O]) :-
		negacja(G,GN),
		\+ member(GN,O),
		bezTautologiiPom(O).

% iteruje po liscie klauzul z negatywnym wystapieniem
mniejszaRezolucja(Z,P,LN,W) :-
	mniejszaRezolucja(Z,P,LN,[],R),
	reverse(R,W).

	mniejszaRezolucja(_,_,[],A,A) :- !.

	mniejszaRezolucja(Z,P,[G|O],A,W) :-
		zamianaDrzewoNaKlauzule(P,DP),
		zamianaDrzewoNaKlauzule(G,DN),
		resolve(Z,DP,DN,REZ),
		\+ bezTautologii(REZ),
		mniejszaRezolucja(Z,P,O,A,W).

	mniejszaRezolucja(Z,P,[G|O],A,W) :-
		zamianaDrzewoNaKlauzule(P,DP),
		zamianaDrzewoNaKlauzule(G,DN),
		resolve(Z,DP,DN,REZ),
		bezTautologii(REZ),
		Rezolwenta = rez(P,G,Z,REZ),
		append([Rezolwenta],A,A2),
		mniejszaRezolucja(Z,P,O,A2,W).

% iteruje po liscie klauzul z pozytywnym wystapieniem
malaRezolucja(Z,LP,LN,W) :-
	malaRezolucja(Z,LP,LN,[],R),
	reverse(R,W).

	malaRezolucja(_,[],_,A,A) :- !.
	malaRezolucja(Z,[G|O],LN,A,W) :-
		mniejszaRezolucja(Z,G,LN,D),
		append(D,A,A2),
		malaRezolucja(Z,O,LN,A2,W).

% zmienne, lista klauzul, rodowod
%?- duzaRezolucja([p,q],[axiom(p v q),axiom(p v ~q), axiom(~p v q), axiom(~p v ~q)],W), last(W,Y).
%W = [rez(axiom(p v q), axiom(~p v q), p, q), rez(axiom(p v ~q), axiom(~p v ~q), p, ~q), rez(rez(axiom(p v q), axiom(~p v q), p, q), rez(axiom(p v ~q), axiom(~p v ~q), p, ~q), q, [])],
%Y = rez(rez(axiom(p v q), axiom(~p v q), p, q), rez(axiom(p v ~q), axiom(~p v ~q), p, ~q), q, []).
duzaRezolucja(Z,K,W) :-
	duzaRezolucja(Z,K,[],R), !,
	reverse(R,W).

	duzaRezolucja([],_,A,A) :- sprzecznosc(A).
	duzaRezolucja([G|O],K,A,RD) :-
		znajdzKlauzule(K,G,KP),
		negacja(G,GN),
		znajdzKlauzule(K,GN,KN),
		subtract(K,KP,W1),
		subtract(W1,KN,W2),
		malaRezolucja(G,KP,KN,R),
		append(R,W2,W3),
		append(R,A,A2),
		duzaRezolucja(O,W3,A2,RD).

% scalenie przodkow na tym samym poziomie
scalanie([G|O],[H|T],[W|R]) :-
	append(G,H,W),
	scalanie(O,T,R).
 
scalanie([],X,X) :- !.
scalanie(X,[],X) :- !.

% rozszczepia przodkow z rodowodu
listaPrzodkow(D,W) :-
	rozdzielenieDrzew(D,R),
	reverse(R,RR),
	flatten(RR,W).

	rozdzielenieDrzew(axiom(X),[[axiom(X)]]).
	rozdzielenieDrzew(rez(P1,P2,Z,L), [[rez(P1,P2,Z,L)]|O]) :-
		rozdzielenieDrzew(P1,LP1),
		rozdzielenieDrzew(P2,LP2),
		scalanie(LP1,LP2,O).

% bierze Clauses, zwraca rodowód
rezolucja(Clauses,Drzewa,Rozdzielone) :-
	zmienneZdaniowe(Clauses,Zmienne),
	sort(Clauses,Powtorzenia),
	axiomId(Powtorzenia,Axiom),

	duzaRezolucja(Zmienne,Axiom,Drzewa),
	last(Drzewa,Ostatni),
	listaPrzodkow(Ostatni,Rozdzielone).

% znajduje numer na liscie
numerNaLiscie(D,K,W) :-
	numerNaLiscie(D,K,1,W).

numerNaLiscie([K|_],K,A,A) :-
	K = axiom(_), !.
numerNaLiscie([K|_],K,A,A) :-
	K = rez(_,_,_,_), !.
numerNaLiscie([_|O],K,A,W) :-
	A2 is A + 1,
	numerNaLiscie(O,K,A2,W).

% generowanie dowodu z numerkami
nadanieNumeru(_,[G],[R]) :-
	G = axiom(L),
	R = (L,axiom), !.
nadanieNumeru(L,[G],[R]) :-
	G = rez(P1,P2,Z,W),
	numerNaLiscie(L,P1,N1),
	numerNaLiscie(L,P2,N2),
	R = (W,(Z,N1,N2)).
nadanieNumeru(L,[G|O],[R|D]) :-
	G = axiom(W),
	R = (W,axiom), !,
	nadanieNumeru(L,O,D).
nadanieNumeru(L,[G|O],[R|D]) :-
	G = rez(P1,P2,Z,W),
	numerNaLiscie(L,P1,N1),
	numerNaLiscie(L,P2,N2),
	R = (W,(Z,N1,N2)),
	nadanieNumeru(L,O,D).

% predykat prove
prove(Clauses,Proof) :-
	rezolucja(Clauses,_,Y),
	nadanieNumeru(Y,Y,Proof).