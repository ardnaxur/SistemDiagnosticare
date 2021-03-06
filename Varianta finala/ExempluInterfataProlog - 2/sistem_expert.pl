%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:-use_module(library(sockets)).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:-use_module(library(lists)).
:-use_module(library(system)).
:-use_module(library(file_systems)).
:-op(900,fy,not).
:-dynamic fapt/3.
:-dynamic interogat/1.
:-dynamic scop/1.
:-dynamic interogabil/3.
:-dynamic regula/3.
:-dynamic intrebare_curenta/3.
:-dynamic solutie/4.
:-dynamic nume/2.
:-dynamic directorOut/1.

close_all:-current_stream(_,_,S),close(S),fail;true.
curata_bc:-current_predicate(P), abolish(P,[force(true)]), fail;true.

%%%%%%%%%%%%%%%%%%%%%%%%%interfata%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
tab(Stream,N):-N>0,write(Stream,' '),N1 is N-1, tab(Stream,N1).
tab(_,0).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

not(P):-P,!,fail.
not(_).

scrie_lista([]) :- nl.
scrie_lista([H|T]) :-
                    write(H), tab(1),
                    scrie_lista(T).

scrie_lista_c([]) :- nl.
scrie_lista_c([H|T]) :- write(' - '), write(H), nl, scrie_lista_c(T).

%%%%%%%%%%%%%%%%%%%%%interfata%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

scrie_lista_c(Stream,[H|T]) :- write(Stream, H), write(Stream,' , '), scrie_lista_c(Stream, T).

scrie_lista(Stream,[]):-nl(Stream),flush_output(Stream).

scrie_lista(Stream,[H|T]) :-
                            write(Stream,H), tab(Stream,1),
                            scrie_lista(Stream,T).

afiseaza_fapte(Stream) :-
                write(Stream,'Fapte existente in baza de cunostinte:'),					%Fapte memora grupul [Atribut Valoare]
                write(Stream, ' (Atribut,valoare) '),
                listeaza_fapte(Stream).


listeaza_fapte(Stream):-
                fapt(av(Atr,Val),FC,_),
                write(Stream,'('),write(Stream,Atr),write(Stream,','),
                write(Stream,Val), write(Stream,')'),
                write(Stream,','), write(Stream,' certitudine '),
                FC1 is integer(FC),write(Stream,FC1),
                nl(Stream),flush_output(Stream), fail.																									% fail e ca sa se intoarca la fapt(...)
listeaza_fapte(Stream).	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

afiseaza_fapte :-
                write('Fapte existente in baza de cunostinte:'),					%Fapte memora grupul [Atribut Valoare]
                nl,nl, write(' (Atribut,valoare) '), nl,nl,
                listeaza_fapte,nl.

listeaza_fapte:-
                fapt(av(Atr,Val),FC,_),
                write('('),write(Atr),write(','),
                write(Val), write(')'),
                write(','), write(' certitudine '),
                FC1 is integer(FC),write(FC1),
                nl,fail.																									% fail e ca sa se intoarca la fapt(...)
listeaza_fapte.																						% echivalent cu sau true ca sa scapam de 'no' returnat de fail

lista_float_int([],[]).
lista_float_int([Regula|Reguli],[Regula1|Reguli1]):-
                                                    (Regula \== utiliz,																				% cuvantul utiliz e in istoric cand faptul e introdus de utilizator, !=utiliz =>dedus =>id regula
                                                    Regula1 is integer(Regula);																% transforma id-ul regulii in int
                                                    Regula ==utiliz, Regula1=Regula),													% punem direct cuvantul utiliz
                                                    lista_float_int(Reguli,Reguli1).

pornire :-
            retractall(interogat(_)),
            retractall(fapt(_,_,_)),
            retractall(intrebare_curenta(_,_,_)),
            write('Introduceti numele dumneavoastra: '),nl, nl, write('|: '), citeste_linie_nume(L), proceseaza_nume(L),
            repeat,
            write('Introduceti una din urmatoarele optiuni: '),
            nl,nl,
            write(' (Incarca Consulta Reinitiaza  Afisare_fapte  Cum   Iesire) '),
            nl,nl,write('|: '),citeste_linie([H|T]),
            executa([H|T]), H == iesire.

proceseaza_nume(L) :- trad_n(R,L,[]), asserta(R), !.
trad_n(nume(Nume,Prenume)) --> [Nume, Prenume].
proceseaza_nume([_]) :- write('Nu ati introdus numele corect! '), write(Stream,'Nu ati introdus numele corect! '), nl.
																																								% optiuni meniu:
executa([incarca]) :- incarca,!,nl,
                      write('Fisierul dorit a fost incarcat'),nl.
executa([consulta]) :- scopuri_princ,!.
executa([reinitiaza]) :-retractall(interogat(_)),
                        retractall(fapt(_,_,_)),!.
executa([afisare_fapte]) :- afiseaza_fapte,!.            %AFISEAZA FAPTELE DIN SISTEMUL EXPERT
						
executa([cum|L]) :- cum(L),!.
executa([iesire]):-!.
executa([_|_]) :- write('Comanda incorecta! '),nl.

scopuri_princ :-scop(Atr),
                determina(Atr), 
                setof(sol(Atr,Val,FC),G^fapt(av(Atr,Val),FC,G),L),
                lista_rev(L,LNou),
                afiseaza_scop(Atr),
                datime(T), datime(Y,M,D,H,Min,S) = T, fapt(av(Atr,Val),_,_),
				prelucrare_timp_ts(Y,M,D,H,Min,S,F),
				creare_t(F,LNou).
				
scopuri_princ:- write('Nu s-au gasit solutii.') .




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%interfata%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

scopuri_princ(Stream) :-scop(Atr), 
                        determina(Stream,Atr), 
                        setof(sol(Atr,Val,FC),G^fapt(av(Atr,Val),FC,G),L), 
                        lista_rev(L,LNou), 
                        afiseaza_scop(Stream,Atr),
						datime(T), datime(Y,M,D,H,Min,S) = T,
						prelucrare_timp_ts(Y,M,D,H,Min,S,F), fapt(av(Atr,Val),_,_), write(Stream,z(F)), nl(Stream),
						creare_t(F,LNou).
						
scopuri_princ(Stream):- write('Nu sunt solutii\n'), write(Stream, n('Nu s-au gasit solutii.')), nl(Stream), flush_output(Stream). 

prelucrare_timp_ts(A1,L1,Z1,O1,M1,S1, F):- number_chars(A1,A), adauga_lista_car('_',A, F1),
										 number_chars(L1,L), adauga_lista_car(F1,L, F2),
										 number_chars(Z1,Z), adauga_lista_car(F2,Z, F3),
										 number_chars(O1,O), adauga_lista_car(F3,O, F4),
										 number_chars(M1,M), adauga_lista_car(F4,M, F5),
										 number_chars(S1,S), adauga_lista_car(F5,S, F).

adauga_lista_car(L,[],L).
adauga_lista_car(F,[H1|T1], F1):- atom_concat(F,H1,F2), adauga_lista_car(F2, T1, F1).

creare_t(Time,LNou):- (directory_exists('output_sistem_expert'),!;										%creare director output
					make_directory('output_sistem_expert'), close_all_streams),
					(directory_exists('output_sistem_expert/utilizatori'),!;				%creare director output
					make_directory('output_sistem_expert/utilizatori'), close_all_streams),
					nume(Nume,Prenume), atom_concat(Prenume, '_', Prenume2), atom_concat(Prenume2, Nume, U), atom_concat('output_sistem_expert/utilizatori/', U, D),
					(directory_exists(D),!;																				%creare director output
					make_directory(D), close_all_streams),
					atom_concat(D, '/',D1), atom_concat('t', Time, T1), atom_concat(D1, T1, Dff), atom_concat(Dff, '.txt', Df),
					open(Df, write, StreamR),close(StreamR),
          atom_concat('d', Time, Dt), atom_concat(D1, Dt, Dff2), atom_concat(Dff2, '.txt', Df2),
          open(Df2, append, StreamRd), scrie_d(StreamRd, Df2, LNou).


scrie_d(StreamRd, Df2, [sol(Atr,Val,FC)|T]):- cum(StreamRd,av(Atr,Val)), close(StreamRd), scrie_d(StreamRd, Df2,T).
scrie_d(StreamRd,Df2,[]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

lista_rev(L1,L2) :- listaaux(L1,[],L2).
listaaux([],Laux,Laux).
listaaux([H|T],Laux,L2) :- listaaux(T,[H|Laux],L2).

determina(Atr) :- realizare_scop(av(Atr,_),_,[scop(Atr)]),!.
determina(_).

%%%%%%%%%%%%%%%%%%%interfata%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
determina(Stream,Atr) :- realizare_scop(Stream,av(Atr,_),_,[scop(Atr)]),!.
determina(_,_).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

afiseaza_scop(Atr) :- nl,fapt(av(Atr,Val),FC,_),
                      FC >= 50,scrie_scop(av(Atr,Val),FC),											% afiseaza doar scopurile relevante (cu FC>=50)
                      nl,fail.

afiseaza_scop(_) :- nl, nl.

scrie_scop(av(Atr,Val),FC) :- solutie(Val, Imagine, Descriere, Contraindicatii),
                            write('Solutie: '), write(Val), nl,
                            write('FC: '), FC1 is integer(FC), write(FC1), nl,
                            write('Detalii: '), write(Descriere), nl,
                            write('Contraindicatii: '), nl,
                            scrie_lista_c(Contraindicatii), nl,
                            write('%%%%%%%%%%%%%%%%%%%%%%%%').

%%%%%%%%%%%%%%%%%%%%%%%%%%interfata%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

afiseaza_scop(Stream, A) :-  nl(Stream),fapt(av(A,Val),FC,_),
                             FC >= 50,scrie_scop(Stream,av(A,Val), FC),fail.  
                         
afiseaza_scop(Stream,_):- nl(Stream), flush_output(Stream).

scrie_scop(Stream,av(Aa,Vall),FC) :- solutie(Vall, Imagine, Descriere, Contraindicatii),
									write(Stream,Imagine), write(Stream,'QQ'),
                                    write(Stream, 'Diagnosticul este ' ), write(Stream,Vall), write(Stream,'QQ'),
                                    write(Stream, 'Factor de Certitudine:'), FC1 is integer(FC), write(Stream, FC1), write(Stream,'QQ'),
                                    write(Stream,Descriere), write(Stream,'QQ'),
                                    write(Stream,'Contraindicatii: '),scrie_lista_c(Stream,Contraindicatii),
									nl(Stream), flush_output(Stream).
                                    %flush_output(Stream).
									
								

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



realizare_scop(not Scop,Not_FC,Istorie) :-  realizare_scop(Scop,FC,Istorie),
					    Not_FC is - FC, !.
						
realizare_scop(Scop,FC,_) :- fapt(Scop,FC,_), !.

realizare_scop(Scop,FC,Istorie) :- pot_interoga(Scop,Istorie),
				   !,realizare_scop(Scop,FC,Istorie).
				   
realizare_scop(Scop,FC_curent,Istorie) :- fg(Scop,FC_curent,Istorie).

%%%%%%%%%%%%%%%%%%%%interfata%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

realizare_scop(Stream,not Scop,Not_FC,Istorie) :- realizare_scop(Stream,Scop,FC,Istorie),
                                                  Not_FC is - FC, !.
realizare_scop(Stream,Scop,FC,_) :- fapt(Scop,FC,_), !.

realizare_scop(Stream,Scop,FC,Istorie) :- pot_interoga(Stream,Scop,Istorie),
                                          !,realizare_scop(Stream,Scop,FC,Istorie).

realizare_scop(Stream,Scop,FC_curent,Istorie) :- fg(Stream,Scop,FC_curent,Istorie).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
						
fg(Scop,FC_curent,Istorie) :- regula(N, premise(Lista),
                            concluzie(Scop,FC)),
                            demonstreaza(N,Lista,FC_premise,Istorie),
                            ajusteaza(FC,FC_premise,FC_nou),
                            actualizeaza(Scop,FC_nou,FC_curent,N),
                            FC_curent == 100,!.

fg(Scop,FC,_) :- fapt(Scop,FC,_).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%interfata%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
fg(Stream,Scop,FC_curent,Istorie) :- regula(N, premise(Lista), concluzie(Scop,FC)),
                                    demonstreaza(Stream,N,Lista,FC_premise,Istorie),
                                    ajusteaza(FC,FC_premise,FC_nou),
                                    actualizeaza(Scop,FC_nou,FC_curent,N),
                                    FC_curent == 100,!.

fg(Stream,Scop,FC,_) :- fapt(Scop,FC,_).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pot_interoga(av(Atr,_),Istorie) :- not interogat(av(Atr,_)),
                                    interogabil(Atr,Mesaj,Optiuni),
                                    interogheaza(Atr,Mesaj,Optiuni,Istorie),nl,
                                    asserta( interogat(av(Atr,_)) ).

%%%%%%%%%%%%%%%%%%%%%%%%interfata%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
pot_interoga(Stream,av(Atr,_),Istorie) :- not interogat(av(Atr,_)),
                                        interogabil(Atr,Mesaj, Optiuni),
                                        interogheaza(Stream,Atr,Mesaj,Optiuni,Istorie),nl(Stream),
                                        asserta( interogat(av(Atr,_)) ).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
						
cum([]) :- write('Scop? '),nl,
            write('|:'),citeste_linie(Linie),nl,
            transformare(Scop,Linie), cum(Scop).
cum(L) :- transformare(Scop,L),nl, cum(Scop).
cum(not Scop) :- fapt(Scop,FC,Reguli),																									% Reguli - vezi Istoric
                    lista_float_int(Reguli,Reguli1),
                    FC < -50,transformare(not Scop,PG),																		% verificam sa fie relevant, un FC sub 50 este irelevant
                    append(PG,[a,fost,derivat,cu, ajutorul, 'regulilor: '|Reguli1],LL),
                    scrie_lista(LL),nl,afis_reguli(Reguli),fail.													% fail - intoarce la fapt
cum(Scop) :- fapt(Scop,FC,Reguli),
            lista_float_int(Reguli,Reguli1),
            FC > 50,transformare(Scop,PG),
            append(PG,[a,fost,derivat,cu, ajutorul, 'regulilor: '|Reguli1],LL),
            scrie_lista(LL),nl,afis_reguli(Reguli),
            fail.
cum(_).

afis_reguli([]).
afis_reguli([N|X]) :- afis_regula(N),
                        premisele(N),
                        afis_reguli(X).
afis_regula(N) :- regula(N, premise(Lista_premise),
                    concluzie(Scop,FC)),NN is integer(N),
                    scrie_lista(['regula  ',NN]),
                    scrie_lista(['  Daca']),
                    scrie_lista_premise(Lista_premise),				%cerinta f
                    scrie_lista(['  Atunci']),
                    transformare(Scop,Scop_tr),
                    append(['   '],Scop_tr,L1),
                    FC1 is integer(FC),append(L1,[FC1],LL),
                    scrie_lista(LL),nl.

scrie_lista_premise([]).																%lista_premise - perechi tip av
scrie_lista_premise([H|T]) :- transformare(H,H_tr),
                                tab(5),scrie_lista(H_tr),
                                scrie_lista_premise(T).																	%in scrie_lista_premise facem transformare2 pt regulile noastre

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%fisier demonstratie%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

cum(StreamRd, not Scop) :- fapt(Scop,FC,Reguli),																									% Reguli - vezi Istoric
                    lista_float_int(Reguli,Reguli1),
                    FC < -50,transformareDiagnostic(not Scop,PG),																		% verificam sa fie relevant, un FC sub 50 este irelevant
                    append(PG,[a,fost,derivat,cu, ajutorul, 'regulilor: '|Reguli1],LL),
                    scrie_lista(StreamRd,LL),
                    nl(StreamRd), afis_reguli(StreamRd,Reguli),fail.													% fail - intoarce la fapt
cum(StreamRd,Scop) :- fapt(Scop,FC,Reguli),
                      lista_float_int(Reguli,Reguli1),
                      FC > 50,transformareDiagnostic(Scop,PG),
                      append(PG,[a,fost,derivat,cu, ajutorul, 'regulilor: '|Reguli1],LL),
                      scrie_lista(StreamRd,LL),
                      afis_reguli(StreamRd,Reguli), fail.
cum(StreamRd,_).

afis_reguli(StreamRd,[]):-write(Stream,'\n').
afis_reguli(StreamRd,[N|X]) :- afis_regula(StreamRd, N),
                        premisele(StreamRd,N),
                        afis_reguli(StreamRd,X).
afis_regula(StreamRd,N) :- regula(N, premise(Lista_premise),concluzie(Scop,FC)),
                          NN is integer(N),scrie_lista(StreamRd,['Id_regula@',NN]),
                    scrie_lista(StreamRd,['premise:']),
                    scrie_lista_premise(StreamRd,Lista_premise), 				%cerinta f
                    transformare(Scop,Scop_tr),
                    append(Scop_tr,['//FC'],L1),
                    FC1 is integer(FC), scrie_lista(StreamRd, L1), write(StreamRd,FC1), write('&&**').

scrie_lista_premise(StreamRd,[]).																%lista_premise - perechi tip av
scrie_lista_premise(StreamRd,[H|T]) :- transformare(H,H_tr),
                                write(StreamRd, '[#]'), scrie_lista(StreamRd,H_tr),
                                scrie_lista_premise(StreamRd, T).																	%in scrie_lista_premise facem transformare2 pt regulile noastre

premisele(StreamRd,N) :- regula(N, premise(Lista_premise), _),
                !, cum_premise(StreamRd,Lista_premise).

cum_premise(StreamRd,[]).
cum_premise(StreamRd,[Scop|X]) :- cum(StreamRd,Scop),cum_premise(StreamRd,X).

transformare(av(A,da),[A]):-!.
transformare(not av(A,da), [not,'[',Atr,']']) :- !.
%transformare(av(A,nu),[not,A]) :- !.										% Nu ajunge pe ramura asta din cauza cut-ului de deasupra
transformare(av(A,V),[A,<,-,V]).

transformareDiagnostic(av(A,V),[A,=,V]).


premisele(N) :- regula(N, premise(Lista_premise), _),
                !, cum_premise(Lista_premise).

cum_premise([]).
cum_premise([Scop|X]) :- cum(Scop),
                        cum_premise(X).

interogheaza(Atr,Mesaj,[da,nu],Istorie) :- !,write(Mesaj),nl,
                                            citeste_opt(X, [da, nu, nu_stiu, nu_conteaza], Istorie),
%					    					de_la_utiliz(X,Istorie,[da,nu,nu_stiu,nu_conteaza]),
                                            det_val_fc(X,Val,FC),
                                            asserta( fapt(av(Atr,Val),FC,[utiliz]) ).

interogheaza(Atr,Mesaj,Optiuni,Istorie) :- write(Mesaj),nl,
                                            citeste_opt(VLista,Optiuni,Istorie),
                                            assert_fapt(Atr,VLista).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%interfata%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
scrie_lista_premise(_,[]).

scrie_lista_premise(Stream,[H|T]) :-
	transformare(H,H_tr),
	tab(Stream,5),scrie_lista(Stream,H_tr),
	scrie_lista_premise(Stream,T).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
						
transformare(av(A,da),[A]) :- !.
transformare(not av(A,da), [not,A]) :- !.
% transformare(av(A,nu),[not,A]) :- !.										% Nu ajunge pe ramura asta din cauza cut-ului de deasupra
transformare(av(A,V),[A,este,V]).

premisele(N) :- regula(N, premise(Lista_premise), _),
                !, cum_premise(Lista_premise).

cum_premise([]).
cum_premise([Scop|X]) :- cum(Scop),
                        cum_premise(X).

interogheaza(Atr,Mesaj,[da,nu],Istorie) :- !,write(Mesaj),nl,
                                            citeste_opt(X, [da, nu, nu_stiu, nu_conteaza], Istorie),
%					    					de_la_utiliz(X,Istorie,[da,nu,nu_stiu,nu_conteaza]),
                                            det_val_fc(X,Val,FC),
                                            asserta( fapt(av(Atr,Val),FC,[utiliz]) ).

interogheaza(Atr,Mesaj,Optiuni,Istorie) :- write(Mesaj),nl,
                                            citeste_opt(VLista,Optiuni,Istorie),
                                            assert_fapt(Atr,VLista).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%interfata%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
       
interogheaza(Stream,Atr,Mesaj,[da,nu],Istorie) :-
	!,write(Stream,i(Mesaj)),nl(Stream),flush_output(Stream),
	write('\n Intrebare atr boolean\n'),
	citeste_opt(Stream, X, [da, nu, nu_stiu, nu_conteaza], Istorie),
	%de_la_utiliz(Stream,X,Istorie,[da,nu]),
	det_val_fc(X,Val,FC),
	asserta( fapt(av(Atr,Val),FC,[utiliz]) ).

interogheaza(Stream,Atr,Mesaj,Optiuni,Istorie) :-
	write('\n Intrebare atr val multiple\n'),
	write(Stream,i(Mesaj)),nl(Stream),flush_output(Stream),
	citeste_opt(Stream,VLista,Optiuni,Istorie),
	assert_fapt(Atr,VLista).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

citeste_opt(X,Optiuni,Istorie) :-  append(['('],Optiuni,Opt1),
                                    append(Opt1,[')'],Opt),
                                    scrie_lista(Opt),
                                    de_la_utiliz(X,Istorie,Optiuni).

de_la_utiliz(X,Istorie,Lista_opt) :- repeat,write(': '),citeste_linie(X),
				     proceseaza_raspuns(X,Istorie,Lista_opt).

%%%%%%%%%%%%%%%%%%%%%%%%%%interfata%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
citeste_opt(Stream,X,Optiuni,Istorie) :- append(['('],Optiuni,Opt1),
                                        append(Opt1,[')'],Opt),
                                        scrie_lista(Stream,Opt),
                                        de_la_utiliz(Stream,X,Istorie,Optiuni).

de_la_utiliz(Stream,X,Istorie,Lista_opt) :-
	repeat,write('Astept raspuns\n'),citeste_linie(Stream,X),format('Am citit ~p din optiunile ~p\n',[X,Lista_opt]),
	proceseaza_raspuns(X,Istorie,Lista_opt), write('gata de la utiliz\n').
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
						
proceseaza_raspuns([de_ce],Istorie,_) :- nl,afis_istorie(Istorie),!,fail.

proceseaza_raspuns([X],_,Lista_opt):- member(X,Lista_opt).
                                      proceseaza_raspuns([X,fc,FC],_,Lista_opt):-
                                      member(X,Lista_opt),float(FC).

assert_fapt(Atr,[Val,fc,FC]) :- !,asserta( fapt(av(Atr,Val),FC,[utiliz]) ).
                                assert_fapt(Atr,[Val]) :-
                                asserta( fapt(av(Atr,Val),100,[utiliz])).

det_val_fc([nu],da,-100).
det_val_fc([nu,FC],da,NFC) :- NFC is -FC.
det_val_fc([nu,fc,FC],da,NFC) :- NFC is -FC.
det_val_fc([Val,FC],Val,FC).
det_val_fc([Val,fc,FC],Val,FC).
det_val_fc([Val],Val,100).

afis_istorie([]) :- nl.
afis_istorie([scop(X)|T]) :- scrie_lista([scop,X]),!,
                            afis_istorie(T).
                            afis_istorie([N|T]) :-
                            afis_regula(N),!,afis_istorie(T).

demonstreaza(N,ListaPremise,Val_finala,Istorie) :- dem(ListaPremise,100,Val_finala,[N|Istorie]),!.

%%%%%%%%%%%%%%%%%%%%%%interfata%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
demonstreaza(Stream,N,ListaPremise,Val_finala,Istorie) :-
                        dem(Stream,ListaPremise,100,Val_finala,[N|Istorie]),!.

dem(_,[],Val_finala,Val_finala,_).

dem(Stream,[H|T],Val_actuala,Val_finala,Istorie) :-realizare_scop(Stream,H,FC,Istorie),
                                                Val_interm is min(Val_actuala,FC),
                                                Val_interm >= 50,
                                                dem(Stream,T,Val_interm,Val_finala,Istorie).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

dem([],Val_finala,Val_finala,_).
dem([H|T],Val_actuala,Val_finala,Istorie) :- realizare_scop(H,FC,Istorie),
                                            Val_interm is min(Val_actuala,FC),
                                            Val_interm >= 50,
                                            dem(T,Val_interm,Val_finala,Istorie).
						
actualizeaza(Scop,FC_nou,FC,RegulaN) :- fapt(Scop,FC_vechi,_),
                                        combina(FC_nou,FC_vechi,FC),
                                        retract( fapt(Scop,FC_vechi,Reguli_vechi) ),
                                        asserta( fapt(Scop,FC,[RegulaN | Reguli_vechi]) ),!.
                                        actualizeaza(Scop,FC,FC,RegulaN) :-
                                        asserta( fapt(Scop,FC,[RegulaN]) ).

ajusteaza(FC1,FC2,FC) :- X is FC1 * FC2 / 100,
                        FC is round(X).

combina(FC1,FC2,FC) :- FC1 >= 0,FC2 >= 0,
                        X is FC2*(100 - FC1)/100 + FC1,
                        FC is round(X).

combina(FC1,FC2,FC) :- FC1 < 0,FC2 < 0,
                        X is - ( -FC1 -FC2 * (100 + FC1)/100),
                        FC is round(X).

combina(FC1,FC2,FC) :- (FC1 < 0; FC2 < 0),
                        (FC1 > 0; FC2 > 0),
                        FCM1 is abs(FC1),FCM2 is abs(FC2),
                        MFC is min(FCM1,FCM2),
                        X is 100 * (FC1 + FC2) / (100 - MFC),
                        FC is round(X).

incarca :- write('Introduceti numele fisierului care doriti sa fie incarcat: '),nl, write('|:'),read(F),
            file_exists(F),!,incarca(F).

incarca:-write('Nume incorect de fisier! '),nl,fail.
/*
incarca(F) :-
						retractall(interogat(_)),retractall(fapt(_,_,_)),
						retractall(scop(_)),retractall(interogabil(_,_,_)),
						retractall(regula(_,_,_)),
						see(F),incarca_reguli,seen,!.
*/

%%%%%%%%%%%%%%%%%%%%interfata%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
incarca(F) :- retractall(interogat(_)),retractall(fapt(_,_,_)),
                retractall(scop(_)),retractall(interogabil(_,_,_)),
                retractall(regula(_,_,_)),
                open(F,read,StreamR),incarca_reguli(StreamR),close(StreamR),!.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

incarca_reguli :- repeat,citeste_propozitie(L),
                    proceseaza(L),L == [end_of_file],nl.

%%%%%%%%%%%%%%%%%%%%%%%interfata%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
incarca_reguli(StreamR) :- repeat,citeste_propozitie(StreamR, L),write(L),
                            proceseaza(L),L == [end_of_file],nl.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
						
proceseaza([end_of_file]):-!.
proceseaza(L) :- trad(R,L,[]),assertz(R), !.
trad(scop(X)) --> ['[',scop,'=','=',X,']'].
trad(interogabil(Atr,P,M)) --> ['[',Atr,'#'],afiseaza(P),lista_optiuni(M).
trad(regula(N,premise(Daca),concluzie(Atunci,F))) --> identificator(N),daca(Daca),atunci(Atunci,F).
trad('Eroare la parsare'-L,L,_).

lista_optiuni(M) --> ['#'],lista_de_optiuni(M).
lista_de_optiuni([Element]) -->  [Element,']'].
lista_de_optiuni([Element|T]) --> [Element,'|','|'],lista_de_optiuni(T).

afiseaza([]) --> [].
afiseaza(P) --> [P].
identificator(N) --> [id_regula,'@',N].

daca(Daca) --> [premise,':'],lista_premise(Daca).

lista_premise([Daca]) --> ['[','#',']'], propoz(Daca).
lista_premise([Prima|Celalalte]) --> ['[','#',']'], propoz(Prima),lista_premise(Celalalte).

atunci(av(Atr,Val),FC) --> [Atr, '=', Val,'/','/',fc,'=',FC].
% atunci(av(Atr,Val),100) --> [Atr, '=', Val]. 	% aici scriem desfacut propoz, propoz nu va exista la noi pt ca noi nu avem concluzii cu not

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%incarcare input (solutii) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%interfata%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
incarca_input(F) :- retractall(solutie(_,_,_,_)),
                    open(F,read,StreamR),
                    incarca_solutii(StreamR),   
                    close(StreamR),!.
incarca_solutii(StreamR) :- repeat,
                            citeste_linie(StreamR,L),
                            (L==[end_of_file],nl ; incarca_solutii_aux(StreamR,L, Lf)).

incarca_solutii_aux(StreamR,L,Lf) :- citeste_linie(StreamR,Laux), 
                                     concat(L,Laux,Lf), 
                                     (Laux==['-','-','-'], (proceseaza_s(Lf), incarca_solutii(StreamR)); incarca_solutii_aux(StreamR,Lf,_)).

citeste_linie(Stream,[Cuv|Lista_cuv]) :-get_code(Stream,Car),
                                        citeste_cuvant(Stream,Car, Cuv, Car1), 
                                        rest_cuvinte_linie(Stream,Car1, Lista_cuv).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/*
incarca_input(F) :- retractall(solutie(_,_,_,_)),see(F), incarca_solutii,seen,!.
*/
incarca_solutii :- repeat, citeste_linie(L), ( L==[end_of_file], nl; incarca_solutii_aux(L, Lf) ).
incarca_solutii_aux(L,Lf) :- citeste_linie(Laux), concat(L,Laux,Lf), (Laux==['-','-','-'], (proceseaza_s(Lf), incarca_solutii); incarca_solutii_aux(Lf,_)).

concat([H|T], X, [H|Trez]):- concat(T, X, Trez).
concat([], L, L).

proceseaza_s([end_of_file]) :- !.
proceseaza_s(L) :- trad_s(R,L,[]),assertz(R), !.
																																								% PARSARE:

trad_s(solutie(Diagnostic,Imagine,Descriere,Contraindicatii)) --> ['[',Diagnostic,']','[',Imagine,']','[',Descriere,']'], lista_contraindicatii(Contraindicatii).
lista_contraindicatii(C) --> ['[',contraindicatii,':'], lista_de_contraindicatii(C).
trad_s('Eroare la parsare'-L,L,_).

lista_de_contraindicatii([Element]) -->  ['-','[',Element,']',']', '-', '-', '-'].
lista_de_contraindicatii([Element|T]) --> ['-', '[', Element, ']'],lista_de_contraindicatii(T).

citeste_linie([Cuv|Lista_cuv]) :- get_code(Car),
                                    citeste_cuvant(Car, Cuv, Car1),
                                    rest_cuvinte_linie(Car1, Lista_cuv).

propoz(not av(Atr,da)) --> [not,'[',Atr,']'].
propoz(av(Atr,Val)) --> [Atr,'<','-',Val].
propoz(av(Atr,da)) --> [Atr].

% -1 este codul ASCII pt EOF

rest_cuvinte_linie(-1, []):-!.
rest_cuvinte_linie(Car,[]) :-(Car==13;Car==10), !.
rest_cuvinte_linie(Car,[Cuv1|Lista_cuv]) :- citeste_cuvant(Car,Cuv1,Car1),
					    rest_cuvinte_linie(Car1,Lista_cuv).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%interfata%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
       
% -1 este codul ASCII pt EOF

rest_cuvinte_linie(_,-1, []):-!.
rest_cuvinte_linie(_,Car,[]) :-(Car==13;Car==10), !.

rest_cuvinte_linie(Stream,Car,[Cuv1|Lista_cuv]) :-
citeste_cuvant(Stream,Car,Cuv1,Car1),      
rest_cuvinte_linie(Stream,Car1,Lista_cuv).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
							
citeste_propozitie([Cuv|Lista_cuv]) :- get_code(Car),citeste_cuvant(Car, Cuv, Car1),
                                        rest_cuvinte_propozitie(Car1, Lista_cuv).

%%%%%%%%%%%%%%%%%%interfata%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

citeste_propozitie(Stream, [Cuv|Lista_cuv]) :-  get_code(Stream, Car),citeste_cuvant(Stream, Car, Cuv, Car1), 
                                                rest_cuvinte_propozitie(Stream, Car1, Lista_cuv).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
							
rest_cuvinte_propozitie(-1, []):-!.
rest_cuvinte_propozitie(Car,[]) :-Car==46, !.
rest_cuvinte_propozitie(Car,[Cuv1|Lista_cuv]) :- citeste_cuvant(Car,Cuv1,Car1),
                                                rest_cuvinte_propozitie(Car1,Lista_cuv).

citeste_cuvant(-1,end_of_file,-1):-!.
citeste_cuvant(Caracter,Cuvant,Caracter1) :- caracter_cuvant(Caracter),!,
                                            name(Cuvant, [Caracter]),get_code(Caracter1).
citeste_cuvant(Caracter, Numar, Caracter1) :- caracter_numar(Caracter),!,
                                            citeste_tot_numarul(Caracter, Numar, Caracter1).

citeste_tot_numarul(Caracter,Numar,Caracter1):- determina_lista(Lista1,Caracter1),
                                                append([Caracter],Lista1,Lista),
                                                transforma_lista_numar(Lista,Numar).

determina_lista(Lista,Caracter1):- get_code(Caracter),
                                    (caracter_numar(Caracter),
                                    determina_lista(Lista1,Caracter1),
                                    append([Caracter],Lista1,Lista);
                                    \+(caracter_numar(Caracter)),
                                    Lista=[],Caracter1=Caracter).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%interfata%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
rest_cuvinte_propozitie(_,-1, []):-!.
    
rest_cuvinte_propozitie(_,Car,[]) :-Car==46, !.

rest_cuvinte_propozitie(Stream,Car,[Cuv1|Lista_cuv]) :-
                                    citeste_cuvant(Stream,Car,Cuv1,Car1),      
                                    rest_cuvinte_propozitie(Stream,Car1,Lista_cuv).


citeste_cuvant(_,-1,end_of_file,-1):-!.

citeste_cuvant(Stream,Caracter,Cuvant,Caracter1) :-   caracter_cuvant(Caracter),!, 
                                                      name(Cuvant, [Caracter]),get_code(Stream,Caracter1).

citeste_cuvant(Stream,Caracter, Numar, Caracter1) :- caracter_numar(Caracter),!,
                                                     citeste_tot_numarul(Stream,Caracter, Numar, Caracter1).
 

citeste_tot_numarul(Stream,Caracter,Numar,Caracter1):-
                                        determina_lista(Stream,Lista1,Caracter1),
                                        append([Caracter],Lista1,Lista),
                                        transforma_lista_numar(Lista,Numar).


determina_lista(Stream,Lista,Caracter1):-get_code(Stream,Caracter), 
                                        (caracter_numar(Caracter),
                                        determina_lista(Stream,Lista1,Caracter1),
                                        append([Caracter],Lista1,Lista); 
                                        \+(caracter_numar(Caracter)),
                                        Lista=[],Caracter1=Caracter).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
							
transforma_lista_numar([],0).
transforma_lista_numar([H|T],N):- transforma_lista_numar(T,NN),
                                    lungime(T,L), Aux is exp(10,L),
                                    HH is H-48,N is HH*Aux+NN.

lungime([],0).
lungime([_|T],L):- lungime(T,L1), L is L1+1.

tab(N):-N>0,write(' '), N1 is N-1, tab(N1).
tab(0).

% 39 este codul ASCII pt apostrof


citeste_cuvant(Caracter,Cuvant,Caracter1) :-
							Caracter==39,!,
							pana_la_urmatorul_apostrof(Lista_caractere),
							L=[Caracter|Lista_caractere],
							name(Cuvant, L),get_code(Caracter1).

pana_la_urmatorul_apostrof(Lista_caractere):-
							get_code(Caracter),
							(Caracter == 39,Lista_caractere=[Caracter];
							Caracter\==39,
							pana_la_urmatorul_apostrof(Lista_caractere1),
							Lista_caractere=[Caracter|Lista_caractere1]).

citeste_cuvant(Caracter,Cuvant,Caracter1) :-
							caractere_in_interiorul_unui_cuvant(Caracter),!,
							((Caracter>64,Caracter<91),!,
							Caracter_modificat is Caracter+32;
							Caracter_modificat is Caracter),
							citeste_intreg_cuvantul(Caractere,Caracter1),
							name(Cuvant,[Caracter_modificat|Caractere]).

citeste_intreg_cuvantul(Lista_Caractere,Caracter1) :-
							get_code(Caracter),
							(caractere_in_interiorul_unui_cuvant(Caracter),
							((Caracter>64,Caracter<91),!,
							Caracter_modificat is Caracter+32;
							Caracter_modificat is Caracter),
							citeste_intreg_cuvantul(Lista_Caractere1, Caracter1),
							Lista_Caractere=[Caracter_modificat|Lista_Caractere1]; \+(caractere_in_interiorul_unui_cuvant(Caracter)),
							Lista_Caractere=[], Caracter1=Caracter).

citeste_cuvant(_,Cuvant,Caracter1) :-
							get_code(Caracter),
							citeste_cuvant(Caracter,Cuvant,Caracter1).
							
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%interfata%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
citeste_cuvant(Stream,Caracter,Cuvant,Caracter1) :-
            Caracter==39,!,
            pana_la_urmatorul_apostrof(Stream,Lista_caractere),
            L=[Caracter|Lista_caractere],
            name(Cuvant, L),get_code(Stream,Caracter1).
        

pana_la_urmatorul_apostrof(Stream,Lista_caractere):-
            get_code(Stream,Caracter),
            (Caracter == 39,Lista_caractere=[Caracter];
            Caracter\==39,
            pana_la_urmatorul_apostrof(Stream,Lista_caractere1),
            Lista_caractere=[Caracter|Lista_caractere1]).


citeste_cuvant(Stream,Caracter,Cuvant,Caracter1) :-          
            caractere_in_interiorul_unui_cuvant(Caracter),!,              
            ((Caracter>64,Caracter<91),!,
            Caracter_modificat is Caracter+32;
            Caracter_modificat is Caracter),                              
            citeste_intreg_cuvantul(Stream,Caractere,Caracter1),
            name(Cuvant,[Caracter_modificat|Caractere]).
        

citeste_intreg_cuvantul(Stream,Lista_Caractere,Caracter1) :-
            get_code(Stream,Caracter),
            (caractere_in_interiorul_unui_cuvant(Caracter),
            ((Caracter>64,Caracter<91),!, 
            Caracter_modificat is Caracter+32;
            Caracter_modificat is Caracter),
            citeste_intreg_cuvantul(Stream,Lista_Caractere1, Caracter1),
            Lista_Caractere=[Caracter_modificat|Lista_Caractere1]; \+(caractere_in_interiorul_unui_cuvant(Caracter)),
            Lista_Caractere=[], Caracter1=Caracter).


citeste_cuvant(Stream,_,Cuvant,Caracter1) :-                
            get_code(Stream,Caracter),       
            citeste_cuvant(Stream,Caracter,Cuvant,Caracter1).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

caracter_cuvant(C):-member(C,[44,59,58,63,33,46,41,40, 91, 93, 35, 124, 47, 61, 64, 60, 45]).

% am specificat codurile ASCII pentru , ; : ? ! . ) (

caractere_in_interiorul_unui_cuvant(C):- C>64,C<91;C>47,C<58;
					C==45;C==95;C>96,C<123.
caracter_numar(C):-C<58,C>=48.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
citeste_linie_nume(Stream, [Cuv|Lista_cuv]) :- get_code(Stream, Car),citeste_nume(Stream, Car, Cuv, Car1),rest_cuvinte_linie_nume(Stream,Car1, Lista_cuv).

rest_cuvinte_linie_nume(_, -1, []) :- !.
rest_cuvinte_linie_nume(Stream,Car,[]) :- (Car==13;Car==10), !.
rest_cuvinte_linie_nume(Stream,Car,[Cuv1|Lista_cuv]) :- citeste_nume(Stream,Car,Cuv1,Car1), rest_cuvinte_linie_nume(Stream,Car1,Lista_cuv).

citeste_nume(_,-1,end_of_file,-1):-!.
citeste_nume(Stream,Caracter,Cuvant,Caracter1) :- caracter_cuvant(Caracter),!, name(Cuvant, [Caracter]),get_code(Stream,Caracter1).
citeste_nume(Stream,Caracter, Numar, Caracter1) :- caracter_numar(Caracter),!, name(Cuvant, [Caracter]),get_code(Stream,Caracter1).

citeste_nume(Stream,Caracter,Cuvant,Caracter1) :- caractere_in_interiorul_unui_nume(Caracter),!,
													((Caracter>64,Caracter<91),!,Caracter_modificat is Caracter+32;
													Caracter_modificat is Caracter),
													citeste_intreg_numele(Stream,Caractere,Caracter1),
													name(Cuvant,[Caracter_modificat|Caractere]).

citeste_intreg_numele(Stream,Lista_Caractere,Caracter1) :- get_code(Stream,Caracter),
															(caractere_in_interiorul_unui_nume(Caracter),
															((Caracter>64,Caracter<91),!, Caracter_modificat is Caracter+32;Caracter_modificat is Caracter),
															citeste_intreg_numele(Stream,Lista_Caractere1, Caracter1),Lista_Caractere=[Caracter_modificat|Lista_Caractere1];
															\+(caractere_in_interiorul_unui_nume(Caracter)),Lista_Caractere=[], Caracter1=Caracter).

citeste_nume(Stream,_,Cuvant,Caracter1) :-get_code(Stream,Caracter),citeste_nume(Stream,Caracter,Cuvant,Caracter1).

caractere_in_interiorul_unui_nume(C):- C>64,C<91; C==45;C>96,C<123.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

inceput:- format('Salutare\n',[]),	flush_output,
            prolog_flag(argv, [PortSocket|_]), %preiau numarul portului, dat ca argument cu -a
            %portul este atom, nu constanta numerica, asa ca trebuie sa il convertim la numar
            atom_chars(PortSocket,LCifre),
            number_chars(Port,LCifre),%transforma lista de cifre in numarul din 
            socket_client_open(localhost: Port, Stream, [type(text)]),
            proceseaza_text_primit(Stream,0).
				
				
proceseaza_text_primit(Stream,C):-
				write(inainte_de_citire),
				read(Stream,CevaCitit),
				write(dupa_citire),
				write(CevaCitit),nl,
				proceseaza_termen_citit(Stream,CevaCitit,C).
				

proceseaza_termen_citit(Stream,director(D),C):- %pentru a seta directorul curent
				format(Stream,'Locatia curenta de lucru s-a deplasat la adresa ~p.',[D]),
				format('Locatia curenta de lucru s-a deplasat la adresa ~p',[D]),
				X=current_directory(_,D),
				write(X),
				call(X),
				nl(Stream),
				flush_output(Stream),
				C1 is C+1,
				proceseaza_text_primit(Stream,C1).				

proceseaza_termen_citit(Stream,executa_nume(X),C):-
				write(Stream,'V-ati inregistrat\n'),
				flush_output(Stream),
				proceseaza_nume(X),
				C1 is C+1, 
				proceseaza_text_primit(Stream,C1).
				
proceseaza_termen_citit(Stream, incarca(X),C):-
				write(Stream,'Se incarca regulile...\n'),
				flush_output(Stream),
				incarca(X),
				C1 is C+1,
				write(Stream,'S-au incarcat regulile\n'),
				flush_output(Stream),
				proceseaza_text_primit(Stream,C1).

proceseaza_termen_citit(Stream, incarca_input(X),C):-
				write(Stream,'Se incarca fisierul de input...\n'),
				flush_output(Stream),
				incarca_input(X),
				C1 is C+1,
                write(Stream,'S-a incarcat fisierul de input\n'),
				flush_output(Stream),
				proceseaza_text_primit(Stream,C1).
				
proceseaza_termen_citit(Stream,comanda(consulta),C):-
				write(Stream,'Se incepe consultarea\n'),
				flush_output(Stream),
				scopuri_princ(Stream),
				C1 is C+1, 
				proceseaza_text_primit(Stream,C1).

proceseaza_termen_citit(Stream,fapte,C):-
				write(Stream,'Afisare fapte:\n'),
				flush_output(Stream),
				afiseaza_fapte(Stream),
				C1 is C+1, 
				proceseaza_text_primit(Stream,C1).
				
proceseaza_termen_citit(Stream, X, _):- % cand vrem sa-i spunem "Iesire"
				(X == end_of_file ; X == exit),
				write(gata),nl,
				close(Stream).

proceseaza_termen_citit(Stream, comanda(reset),C):-
				write(Stream,'Resetare sistem.\n'),
				flush_output(Stream),
				executa([reinitiaza]),
				C1 is C+1,
				proceseaza_text_primit(Stream,C1).				
			
proceseaza_termen_citit(Stream, Altceva,C):- %cand ii trimitem sistemului expert o comanda pe care n-o pricepe
				write(Stream,'nu se recunoaste comanda!!!\n'),
				write(Stream,'Parametru necunoscut:'),
				write(Stream,Altceva),nl(Stream),
				flush_output(Stream),
				C1 is C+1,
				proceseaza_text_primit(Stream,C1).

