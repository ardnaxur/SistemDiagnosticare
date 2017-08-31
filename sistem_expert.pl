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


close_all:-current_stream(_,_,S),close(S),fail;true.
curata_bc:-current_predicate(P), abolish(P,[force(true)]), fail;true.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
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
scrie_lista_c([H|T]) :- write(' - '), write(H), nl, scrie_lista(T).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
scrie_lista(Stream,[]):-nl(Stream),flush_output(Stream).

scrie_lista(Stream,[H|T]) :-
write(Stream,H), tab(Stream,1),
scrie_lista(Stream,T).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

afiseaza_fapte :-
					write('Fapte existente in baza de cunostinte:'),											% Fapte memora grupul [Atribut Valoare]
					nl,nl, write(' (Atribut,valoare) '), nl,nl,														% afiseaza headerul listei de fapte
					listeaza_fapte,nl.

listeaza_fapte :-
					fapt(av(Atr,Val),FC,_),																								% afiseaza lista de fapte (Atr, Val, int(FC))
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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



un_pas(Rasp,OptiuniUrm,MesajUrm):-scop(Atr),(Rasp \== null,intreaba_acum(Rasp)
						; true), determina1(Atr,OptiuniUrm,MesajUrm), afiseaza_scop(Atr).

intreaba_acum(Rasp):-intrebare_curenta(Atr,OptiuniV,MesajV),										% pune intrebarea
						interogheaza1(Rasp,Atr,MesajV,OptiuniV,Istorie),nl,
						asserta(interogat(av(Atr,_))).																			% marcheaza ca a pus intrebarea

interogheaza1(X,Atr,Mesaj,[da,nu],Istorie) :- !,de_la_utiliz1(X,Istorie,[da,nu]), %da, nu, nu_stiu, nu_conteaza
						det_val_fc(X,Val,FC),	asserta(fapt(av(Atr,Val),FC,[utiliz]) ).

interogheaza1(VLista,Atr,Mesaj,Optiuni,Istorie) :-
						de_la_utiliz1(VLista,Optiuni,Istorie),
						assert_fapt(Atr,VLista).


%de_la_utiliz1(+Rasp,?Istorie,+Lista_opt)
de_la_utiliz1(X,Istorie,Lista_opt) :- proceseaza_raspuns([X],Istorie,Lista_opt).


determina1(Atr,OptiuniUrm,MesajUrm) :- realizare_scop1(av(Atr,_),_,[scop(Atr)],
						OptiuniUrm,MesajUrm),!.

determina1(_,_,_).

realizare_scop1(not Scop,Not_FC,Istorie,OptiuniUrm,MesajUrm) :-									% transforma FC in -FC pentru not scop
						realizare_scop1(Scop,FC,Istorie,OptiuniUrm,MesajUrm),
						Not_FC is - FC, !.

realizare_scop1(Scop,FC,_,_,_) :- fapt(Scop,FC,_), !.
realizare_scop1(Scop,FC,Istorie,OptiuniUrm,MesajUrm) :-
						pot_interoga1(Scop,Istorie,OptiuniUrm,MesajUrm), !.									% verifica daca se poate interoga pt atributul dat (Scop)

%realizare_scop1(Scop,FC,Istorie,OptiuniUrm,MesajUrm).

realizare_scop1(Scop,FC_curent,Istorie,OptiuniUrm,MesajUrm) :-
						fg1(Scop,FC_curent,Istorie,OptiuniUrm,MesajUrm).


pot_interoga1(av(Atr,_),Istorie, Optiuni, Mesaj) :- not interogat(av(Atr,_)),		% nu a fost deja folosita intrebarea
						interogabil(Atr,Mesaj,Optiuni),																			% exista intrebarea
						retractall(intrebare_curenta(_,_,_)),
						assert(intrebare_curenta(Atr, Optiuni,Mesaj)), !.


pornire1 :- retractall(interogat(_)), 																					% le vom folosi la interfata
						retractall(fapt(_,_,_)),
						retractall(intrebare_curenta(_,_,_)),
						retractall(scop(_)),
						retractall(interogabil(_)),
						retractall(regula(_,_,_)),
						incarca('sist_expert.txt').																					% sist_expert contine reguli


fg1(Scop,FC_curent,Istorie,OptiuniUrm,MesajUrm) :-
						regula(N, premise(Lista), concluzie(Scop,FC)),
						demonstreaza1(N,Lista,FC_premise,Istorie,OptiuniUrm,MesajUrm),
						(nonvar(FC), nonvar(FC_premise),ajusteaza(FC,FC_premise,FC_nou),
						actualizeaza(Scop,FC_nou,FC_curent,N),
						FC_curent == 100; true),!.

fg1(Scop,FC,_,_,_) :- fapt(Scop,FC,_).

demonstreaza1(N,ListaPremise,Val_finala,Istorie,OptiuniUrm,MesajUrm) :-
						dem1(ListaPremise,100,Val_finala,[N|Istorie],OptiuniUrm,MesajUrm),!.

dem1([],Val_finala,Val_finala,_,_,_).

dem1([H|T],Val_actuala,Val_finala,Istorie,OptiuniUrm,MesajUrm) :-
						realizare_scop1(H,FC,Istorie,OptiuniUrm,MesajUrm),
						(nonvar(FC),
						Val_interm is min(Val_actuala,FC),
						Val_interm >= 20,
						dem1(T,Val_interm,Val_finala,Istorie,OptiuniUrm,MesajUrm) ;true).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
pornire :-  retractall(interogat(_)),																						% instantieaza meniu
						retractall(fapt(_,_,_)),
						retractall(intrebare_curenta(_,_,_)),
						repeat,
						write('Introduceti una din urmatoarele optiuni: '),
						nl,nl,
						write(' (Incarca Consulta Reinitiaza  Afisare_fapte  Cum   Iesire)'),
						nl,nl,write('|: '),citeste_linie([H|T]),
						executa([H|T]), H == iesire.
																																								% optiuni meniu:
executa([incarca]) :- incarca,!,nl,
											write('Fisierul dorit a fost incarcat'),nl.

executa([consulta]) :- scopuri_princ,!.

executa([reinitiaza]) :- retractall(interogat(_)), retractall(fapt(_,_,_)),!.

executa([afisare_fapte]) :- afiseaza_fapte,!.	 																	% AFISEAZA FAPTELE DIN SISTEMUL EXPERT

executa([cum|L]) :- cum(L),!.

executa([iesire]):-!.

executa([_|_]) :- write('Comanda incorecta! '), nl.

scopuri_princ :- scop(Atr), determina(Atr),																			% pune intrebarile pentru scop
								 setof(sol(Atr,Val,FC),G^fapt(av(Atr,Val),FC,G),L),							% setof(?Element, :Scop, ?Lista) - pune in Lista toate valorile lui Element care ideplinesc Scop
								 lista_rev(L,LNou), afiseaza_scop(Atr).

scopuri_princ :- write('Nu s-au gasit solutii.').

lista_rev(L1,L2) :- listaaux(L1,[],L2).																					% reverse lista
listaaux([],Laux,Laux).
listaaux([H|T],Laux,L2) :- listaaux(T,[H|Laux],L2).

determina(Atr) :- realizare_scop(av(Atr,_),_,[scop(Atr)]), !.
determina(_).

afiseaza_scop(Atr) :- nl,fapt(av(Atr,Val),FC,_),
											FC >= 20,scrie_scop(av(Atr,Val),FC),											% afiseaza doar scopurile relevante (cu FC>=20)
											nl,fail.

afiseaza_scop(_) :- nl, nl.

scrie_scop(av(Atr,Val),FC) :- solutie(Val, Imagine, Descriere, Contraindicatii),
															write('Solutie: '), write(Val), nl,
															write('FC: '), FC1 is integer(FC), write(FC1), nl,
															write('Detalii: '), write(Descriere), nl,
															write('Contraindicatii: '), nl,
															scrie_lista_c(Contraindicatii), nl,
															write('%%%%%%%%%%%%%%%%%%%%%%%%').


scrie_scop1(av(Atr,Val),FC) :- transformare(av(Atr,Val), X), scrie_lista(X),			% AFISEAZA SOLUTIA % scrie listele (atribut,valoare) ca text pentru un scop
															tab(2),write(' '),write('FC este '),							%scrie_scop1 e sscris de profa si rescris ca scrie_scop
															FC1 is integer(FC),write(FC1).

realizare_scop(not Scop,Not_FC,Istorie) :- realizare_scop(Scop,FC,Istorie),
																					 Not_FC is - FC, !.										% trateaza cazul FC negativ

realizare_scop(Scop,FC,_) :- fapt(Scop,FC,_), !.

realizare_scop(Scop,FC,Istorie) :- pot_interoga(Scop,Istorie), !,
																	 realizare_scop(Scop,FC,Istorie).

realizare_scop(Scop,FC_curent,Istorie) :- fg(Scop,FC_curent,Istorie).

fg(Scop,FC_curent,Istorie) :- regula(N, premise(Lista), concluzie(Scop,FC)),
															demonstreaza(N,Lista,FC_premise,Istorie),
															ajusteaza(FC,FC_premise,FC_nou),
															actualizeaza(Scop,FC_nou,FC_curent,N),
															FC_curent == 100,!.

fg(Scop,FC,_) :- fapt(Scop,FC,_).

pot_interoga(av(Atr,_),Istorie) :- not interogat(av(Atr,_)),
																	 interogabil(Atr,Mesaj,Optiuni),
																	 interogheaza(Atr,Mesaj,Optiuni,Istorie),nl,
																	 asserta( interogat(av(Atr,_)) ).

cum([]) :- write('Scop? '),nl,write('|:'),citeste_linie(Linie),nl,
					 transformare(Scop,Linie), cum(Scop).

cum(L) :- transformare(Scop,L),nl, cum(Scop).

cum(not Scop) :- fapt(Scop,FC,Reguli),																					% Reguli - vezi Istoric
								 lista_float_int(Reguli,Reguli1),
								 FC < -20,transformare(not Scop,PG),														% verificam sa fie relevant, un FC sub 20 este irelevant
								 append(PG,[a,fost,derivat,cu, ajutorul, 'regulilor: '|Reguli1],LL),
								 scrie_lista(LL),nl,afis_reguli(Reguli),fail.										% fail - intoarce la fapt

cum(Scop) :- fapt(Scop,FC,Reguli),lista_float_int(Reguli,Reguli1),FC > 20,
						 transformare(Scop,PG),
						 append(PG,[a,fost,derivat,cu, ajutorul, 'regulilor: '|Reguli1],LL),
						 scrie_lista(LL),nl,afis_reguli(Reguli),fail.
cum(_).

afis_reguli([]).
afis_reguli([N|X]) :- afis_regula(N),premisele(N),afis_reguli(X).
afis_regula(N) :- regula(N, premise(Lista_premise),concluzie(Scop,FC)),
									NN is integer(N),scrie_lista(['regula  ',NN]),
									scrie_lista(['  Daca']),
									scrie_lista_premise(Lista_premise),														% cerinta f
									scrie_lista(['  Atunci']),
									transformare(Scop,Scop_tr),
									append(['   '],Scop_tr,L1),
									FC1 is integer(FC),append(L1,[FC1],LL),
									scrie_lista(LL),nl.

scrie_lista_premise([]).																												% lista_premise - perechi tip av
scrie_lista_premise([H|T]) :- transformare(H,H_tr),tab(5),scrie_lista(H_tr),
															scrie_lista_premise(T).														% in scrie_lista_premise facem transformare2 pt regulile noastre

transformare(av(A,da),[A]) :- !.																								% transforma predicatele (atribut,valoare) in text
transformare(not av(A,da), [not,A]) :- !.
% transformare(av(A,nu),[not,A]) :- !.																					% Nu ajunge pe ramura asta din cauza cut-ului de deasupra
transformare(av(A,V),[A,este,V]).

premisele(N) :- regula(N,premise(Lista_premise),_),!,cum_premise(Lista_premise).

cum_premise([]).
cum_premise([Scop|X]) :- cum(Scop),cum_premise(X).

interogheaza(Atr,Mesaj,[da,nu],Istorie) :-
						!,write(Mesaj),nl,
						citeste_opt(X, [da, nu, nu_stiu, nu_conteaza], Istorie),
%						de_la_utiliz(X,Istorie,[da,nu, nu_stiu, nu_conteaza]),
						det_val_fc(X,Val,FC),
						asserta( fapt(av(Atr,Val),FC,[utiliz]) ).

interogheaza(Atr,Mesaj,Optiuni,Istorie) :- write(Mesaj),nl,
																					 citeste_opt(VLista,Optiuni,Istorie),
																					 assert_fapt(Atr,VLista).

citeste_opt(X,Optiuni,Istorie) :- append(['('],Optiuni,Opt1),
																	append(Opt1,[')'],Opt),
																	scrie_lista(Opt),
																	de_la_utiliz(X,Istorie,Optiuni).

de_la_utiliz(X,Istorie,Lista_opt) :- repeat,write(': '),citeste_linie(X),
																		 proceseaza_raspuns(X,Istorie,Lista_opt).

proceseaza_raspuns([de_ce],Istorie,_) :- nl,afis_istorie(Istorie),!,fail.

proceseaza_raspuns([X],_,Lista_opt) :- member(X,Lista_opt).

proceseaza_raspuns([X,fc,FC],_,Lista_opt) :- member(X,Lista_opt),float(FC).

assert_fapt(Atr,[Val,fc,FC]) :- !,asserta( fapt(av(Atr,Val),FC,[utiliz]) ).

assert_fapt(Atr,[Val]) :- asserta( fapt(av(Atr,Val),100,[utiliz])).

det_val_fc([nu],da,-100).
det_val_fc([nu,FC],da,NFC) :- NFC is -FC.
det_val_fc([nu,fc,FC],da,NFC) :- NFC is -FC.
det_val_fc([Val,FC],Val,FC).
det_val_fc([Val,fc,FC],Val,FC).
det_val_fc([Val],Val,100).

afis_istorie([]) :- nl.
afis_istorie([scop(X)|T]) :- scrie_lista([scop,X]),!,afis_istorie(T).

afis_istorie([N|T]) :- afis_regula(N),!,afis_istorie(T).

demonstreaza(N,ListaPremise,Val_finala,Istorie) :- dem(ListaPremise,100,Val_finala,[N|Istorie]),!.

dem([],Val_finala,Val_finala,_).

dem([H|T],Val_actuala,Val_finala,Istorie) :- realizare_scop(H,FC,Istorie),
																						 Val_interm is min(Val_actuala,FC),
																						 Val_interm >= 20,
																						 dem(T,Val_interm,Val_finala,Istorie).

actualizeaza(Scop,FC_nou,FC,RegulaN) :- fapt(Scop,FC_vechi,_),
																				combina(FC_nou,FC_vechi,FC),
																				retract(fapt(Scop,FC_vechi,Reguli_vechi)),
																				asserta(fapt(Scop,FC,[RegulaN|Reguli_vechi])),!.
actualizeaza(Scop,FC,FC,RegulaN) :- asserta(fapt(Scop,FC,[RegulaN])).

ajusteaza(FC1,FC2,FC) :- X is FC1 * FC2 / 100, FC is round(X).
combina(FC1,FC2,FC) :- FC1 >= 0,FC2 >= 0, X is FC2*(100 - FC1)/100 + FC1,
											 FC is round(X).
combina(FC1,FC2,FC) :- FC1 < 0,FC2 < 0,	X is - ( -FC1 -FC2 * (100 + FC1)/100),
											 FC is round(X).
combina(FC1,FC2,FC) :- (FC1 < 0; FC2 < 0),(FC1 > 0; FC2 > 0),FCM1 is abs(FC1),
											 FCM2 is abs(FC2),MFC is min(FCM1,FCM2),
											 X is 100 * (FC1 + FC2) / (100 - MFC),FC is round(X).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%incarcare reguli%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

incarca :- write('Introduceti numele fisierului care doriti sa fie incarcat: '),nl, write('|:'),read(F),
					 file_exists(F),!,incarca(F).

incarca :- write('Nume incorect de fisier! '),nl,fail.

incarca(F) :- retractall(interogat(_)),retractall(fapt(_,_,_)),retractall(scop(_)),
							retractall(interogabil(_,_,_)),retractall(regula(_,_,_)),see(F),
							incarca_reguli,seen,!.

incarca_reguli :- repeat,citeste_propozitie(L),proceseaza(L),L==[end_of_file],nl.

proceseaza([end_of_file]) :- !.

proceseaza(L) :- trad(R,L,[]),assertz(R), !.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%PARSARE %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
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
% atunci(av(Atr,Val),100) --> [Atr, '=', Val]. 																	% aici scriem desfacut propoz, propoz nu va exista la noi pt ca noi nu avem concluzii cu not

propoz(not av(Atr,da)) --> [not,'[',Atr,']'].
propoz(av(Atr,Val)) --> [Atr,'<','-',Val].
propoz(av(Atr,da)) --> [Atr].


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%incarcare input (solutii) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
incarca_input(F) :- retractall(solutie(_,_,_,_)),see(F), incarca_solutii,seen,!.

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
%%%%%

citeste_linie([Cuv|Lista_cuv]) :- get_code(Car),citeste_cuvant(Car, Cuv, Car1),
																	rest_cuvinte_linie(Car1, Lista_cuv).

% -1 este codul ASCII pt EOF

rest_cuvinte_linie(-1, []) :- !.
rest_cuvinte_linie(Car,[]) :- (Car==13;Car==10), !.
rest_cuvinte_linie(Car,[Cuv1|Lista_cuv]) :- citeste_cuvant(Car,Cuv1,Car1),
																						rest_cuvinte_linie(Car1,Lista_cuv).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

citeste_propozitie([Cuv|Lista_cuv]) :-
							get_code(Car),citeste_cuvant(Car, Cuv, Car1),
							rest_cuvinte_propozitie(Car1, Lista_cuv).

rest_cuvinte_propozitie(-1, []):-!.
rest_cuvinte_propozitie(Car,[]) :-Car==46, !.
rest_cuvinte_propozitie(Car,[Cuv1|Lista_cuv]) :-
							citeste_cuvant(Car,Cuv1,Car1),
							rest_cuvinte_propozitie(Car1,Lista_cuv).

citeste_cuvant(-1,end_of_file,-1):-!.
citeste_cuvant(Caracter,Cuvant,Caracter1) :-
							caracter_cuvant(Caracter),!,
							name(Cuvant, [Caracter]),get_code(Caracter1).
citeste_cuvant(Caracter, Numar, Caracter1) :-
							caracter_numar(Caracter),!,
							citeste_tot_numarul(Caracter, Numar, Caracter1).

citeste_tot_numarul(Caracter,Numar,Caracter1):-
							determina_lista(Lista1,Caracter1),
							append([Caracter],Lista1,Lista),
							transforma_lista_numar(Lista,Numar).

determina_lista(Lista,Caracter1):-
							get_code(Caracter),
							(caracter_numar(Caracter),
							determina_lista(Lista1,Caracter1),
							append([Caracter],Lista1,Lista);
							\+(caracter_numar(Caracter)),
							Lista=[],Caracter1=Caracter).

transforma_lista_numar([],0).
transforma_lista_numar([H|T],N):-
							transforma_lista_numar(T,NN),
							lungime(T,L), Aux is exp(10,L),
							HH is H-48,N is HH*Aux+NN.

lungime([],0).
lungime([_|T],L):-
							lungime(T,L1),
							L is L1+1.

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

caracter_cuvant(C):-member(C,[44,59,58,63,33,46,41,40, 91, 93, 35, 124, 47, 61, 64, 60, 45, 95]).

% am specificat codurile ASCII pentru , ; : ? ! . ) (

caractere_in_interiorul_unui_cuvant(C):-
							C>64,C<91;C>47,C<58;
							C==45;C==95;C>96,C<123.
							caracter_numar(C):-C<58,C>=48.
