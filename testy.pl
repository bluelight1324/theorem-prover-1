:- module(testy, [resolve_tests/5, prove_tests/4]).

:- op(200, fx, ~).
:- op(500, xfy, v).

%% RESOLVE

% krotkie klauzule, wynik pusty
resolve_tests(pusta, p, p, ~p, []).

% krotkie klauzule, wynik niepusty, istnieja inne "pary" poz/neg
resolve_tests(krotkie_pozneg_1, p, p v q v r, ~p v ~q v ~r, q v r v ~q v ~r).
resolve_tests(krotkie_pozneg_2, q, q v r, ~q v ~r v t, r v ~r v t).
resolve_tests(krotkie_pozneg_3, r, p v r, ~p v ~r, p v ~p).
resolve_tests(krotkie_pozneg_4, p, p v ~q v r, ~p v ~q v ~r, ~q v r v ~r).

% dlugie klauzule, wynik niepusty
resolve_tests(dlugie_1, p, p v q v ~r v s v ~t v w, ~p v ~t v w, q v ~r v s v ~t v w).
resolve_tests(dlugie_2, p, p v q v r v s v t v w v x v y v z, ~p, q v r v s v t v w v x v y v z).
resolve_tests(dlugie_3, p, p v q v r v s v t v w v x v y v z, ~p v a v b v c v d v e v f v g, q v r v s v t v w v x v y v z v a v b v c v d v e v f v g).
resolve_tests(dlugie_4, p, p v q v r v s v t, ~p v q v r v s v t, q v r v s v t).

% dlugie klauzule, wynik niepusty, istnieja inne "pary" poz/neg
resolve_tests(dlugie_pozneg_1, p, p v q v ~r v s v ~t v w, ~p v t v ~w, q v ~r v s v ~t v w v t v ~w).
resolve_tests(dlugie_pozneg_2, p, p v q v r v s v t v w v x v y v z, ~p v ~z, q v r v s v t v w v x v y v z v ~z).
resolve_tests(dlugie_pozneg_3, p, p v q v r v s v t v w v x v y v z, ~p v a v b v c v d v e v f v g v ~z, q v r v s v t v w v x v y v z v a v b v c v d v e v f v g v ~z).
resolve_tests(dlugie_pozneg_4, p, p v q v r v s v t, ~p v ~q v ~r v ~s v ~t, q v r v s v t v ~q v ~r v ~s v ~t).

%% PROVE - VALIIDITY

% spelnialne
prove_tests(malo_klauzul_malo_zmiennych_1, validity, [p], sat).
prove_tests(malo_klauzul_malo_zmiennych_2, validity, [~p], sat).

prove_tests(malo_klauzul_malo_zmiennych_3, validity, [p v p], sat).
prove_tests(malo_klauzul_malo_zmiennych_4, validity, [~p v ~p], sat).
prove_tests(malo_klauzul_malo_zmiennych_5, validity, [p v q], sat).
prove_tests(malo_klauzul_malo_zmiennych_6, validity, [p v ~q], sat).
prove_tests(malo_klauzul_malo_zmiennych_7, validity, [~p v ~q], sat).

prove_tests(malo_klauzul_duzo_zmiennych_1, validity, [p v q v r], sat).
prove_tests(malo_klauzul_duzo_zmiennych_2, validity, [p v q v ~r], sat).
prove_tests(malo_klauzul_duzo_zmiennych_3, validity, [p v ~q v ~r], sat).
prove_tests(malo_klauzul_duzo_zmiennych_4, validity, [~p v ~q v ~r], sat).

prove_tests(duzo_klauzul_malo_zmiennych_1, validity, [p, p], sat).
prove_tests(duzo_klauzul_malo_zmiennych_2, validity, [p, q], sat).
prove_tests(duzo_klauzul_malo_zmiennych_3, validity, [p, ~q], sat).
prove_tests(duzo_klauzul_malo_zmiennych_4, validity, [p v q, ~p v q, ~p v ~q], sat).

prove_tests(duzo_klauzul_duzo_zmiennych_1, validity, [~p v r, p v q v r, p v ~q v r], sat).
prove_tests(duzo_klauzul_duzo_zmiennych_2, validity, [p, p v r, r v q, p v ~r], sat).
prove_tests(duzo_klauzul_duzo_zmiennych_3, validity, [~q v r, ~r v p, p v q v r, ~r v ~q v ~p], sat).
prove_tests(duzo_klauzul_duzo_zmiennych_4, validity, [p, ~p v q, ~q v r, ~p v ~r v s], sat).
prove_tests(duzo_klauzul_duzo_zmiennych_5, validity, [p, q, r, s, u, w, ~y, z], sat).

% falszywe
prove_tests(negacja, validity, [p, ~p], unsat).

% tautologie
prove_tests(pusta, validity, [], sat).
prove_tests(wylaczony_srodek_val, validity, [p v ~p], sat).
prove_tests(wiekszy_wylaczony_srodek, validity, [p v ~p v q v r v s], sat).

%% PROVE - PERFORMANCE
prove_tests(duzo_zmiennych, performance, [p, q, r, s, u, w, ~y, z], sat).
prove_tests(wylaczony_srodek_per, performance, [p v ~p v q v r v s v u v w v ~y v z], sat).