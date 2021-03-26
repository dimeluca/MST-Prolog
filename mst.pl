%%%% -*- Mode: Prolog -*-

%%%% mst.pl

:- dynamic graph/1.
:- dynamic arc/4.
:- dynamic vertex/2.
:- dynamic heap/2.
:- dynamic heap_entry/4.
:- dynamic vertex_key/3.
:- dynamic vertex_previous/3.

%%% GRAPH

%%% new_graph/1

new_graph(G) :-
    graph(G),
    writeln('Graph already exist'),
    !.

new_graph(G) :-
    assert(graph(G)),
    !.

%%% new_vertex/2

new_vertex(G, V) :-
    graph(G),
    vertex(G, V).

new_vertex(G, V) :-
    graph(G),
    assert(vertex(G, V)),
    !.

%%% vertices/2

graph_vertices(G, Vs) :-
    graph(G),
    findall(V, vertex(G, V), Xs),
    Vs = Xs.

%%% list_vertices/1

list_vertices(G) :-
    graph(G),
    listing(vertex(G, _)).

%%% new_arc/3

new_arc(G, U, V) :-
    graph(G),
    vertex(_, U),
    vertex(_, V),
    new_arc(G, U, V, 1),
    !.

%%% new_arc/4

new_arc(G, U, V, _) :-
    graph(G),
    arc(G, U, V, _).

new_arc(G, U, V, Weight) :-
    graph(G),
    arc(G, U, V, OldWeight),
    Weight > 0,
    retract(arc(G, U, V, OldWeight)),
    assert(arc(G, U, V, Weight)),
    writeln('Arc weight updated'),
    !.

new_arc(G, U, V, Weight) :-
    graph(G),
    vertex(G, U),
    vertex(G, V),
    Weight > 0,
    assert(arc(G, U, V, Weight)),
    !.


new_arc(G, U, V, Weight) :-
    graph(G),
    vertex(G, U),
    vertex(G, V),
    Weight < 0,
    write('Weight cannot be negative'),
    !.

%%% arcs/2

graph_arcs(G, Es) :-
    graph(G),
    Arc = arc(G, _, _, _),
    findall(Arc, Arc, Es),
    !.

%%% list_arcs/1

list_arcs(G) :-
    graph(G),
    listing(arc(G, _, _, _)), !.

%%% delete_graph/1

delete_graph(G) :-
    graph(G),
    retractall(graph(G)),
    retractall(vertex(G, _)),
    retractall(arc(G, _, _, _)).

%%% neighbors/3

vertex_neighbors(G, V, Ns) :-
    vertex(G, V),
    findall(arc(G, V, N, W), arc(G, V, N, W), Nb1),
    findall(arc(G, V, N, W), arc(G, N, V, W), Nb2),
    append(Nb1, Nb2, Ns),
    !.

%%% adjs/3

adjs(G, V, Vs) :-
    graph(G),
    vertex(G, V),
    findall(vertex(G, Vx), arc(G, V, Vx, _), Vs1),
    findall(vertex(G, Vx), arc(G, Vx, V, _), Vs2),
    append(Vs1, Vs2, Vs),
    !.

%%% list_graph/1

list_graph(G) :-
    graph(G),
    list_vertices(G),
    list_arcs(G).

%%% read_graph/2


read_graph(G, FileName) :-
    new_graph(G),
    csv_read_file(FileName, Data, [separator(0'\t)]),
    create_from_file(G, Data),
    !.

create_from_file(_, []) :- !.

create_from_file(G, Data) :-
    Data = [X | Xs],
    X =.. [_, V1, V2, W],
    new_vertex(G, V1),
    new_vertex(G, V2),
    new_arc(G, V1, V2, W),
    create_from_file(G, Xs),
    !.

%%% write_graph/2

write_graph(G, FileName) :-
    write_graph(G, FileName, graph).

%%% write_graph/3

write_graph(G, FileName, Type) :-
    Type = 'graph',
    graph_arcs(G, Data),
    insert_into_file(G, FileName, Data),
    !.

write_graph(G, FileName, Type) :-
    Type = 'edges',
    insert_into_file(_, FileName, G),
    !.

%%% insert_into_file/3

insert_into_file(_, FileName, Data) :-
    maplist(map_row, Data, Rows),
    csv_write_file(FileName, Rows, [separator(0'\t)]),
    !.

%%% map_row/2

map_row(R, row(V1, V2, W)) :-
    R =.. [_, _, V1, V2, W],
    !.


%%% MINHEAP

%%% new_heap/1

new_heap(H) :-
    heap(H, _S),
    write('Error: Heap already exist'),
    !.

new_heap(H) :-
    assert(heap(H, 0)), !.

%%% delete_heap/1

delete_heap(H) :-
    heap(H, _),
    retract(heap(H, _)),
    retractall(heap_entry(H, _, _, _)),
    !.

delete_heap(_) :- !.


%%% heap_has_size/2
%
heap_has_size(H, S) :-
    heap(H, S).

%%% heap_empty/1

heap_empty(H) :-
    heap(H, 0).

%%% heap_not_empty/1
heap_not_empty(H) :-
    heap(H, S),
    S >= 1.

%%% heap_head/3

heap_head(H, K, V) :-
    heap(H, _),
    heap_not_empty(H),
    heap_entry(H, 1, K, V).

%%% heap_insert/3

heap_insert(H, K, V) :-
    heap(H, S),
    heap_empty(H),
    NewSize is S + 1,
    retract(heap(H, S)),
    assert(heap(H, NewSize)),
    assert(heap_entry(H, 1, K, V)),
    !.

heap_insert(H, K, V) :-
    heap(H, S),
    heap_not_empty(H),
    NewSize is S + 1,
    Father is floor(NewSize / 2),
    heap_entry(H, Father, KFather, _),
    KFather =< K,
    retract(heap(H, S)),
    assert(heap(H, NewSize)),
    assert(heap_entry(H, NewSize, K, V)),
    !.

heap_insert(H, K, V) :-
    heap(H, S),
    NewSize is S + 1,
    retract(heap(H, S)),
    assert(heap(H, NewSize)),
    assert(heap_entry(H, NewSize, K, V)),
    property_maintenance(H, NewSize),
    !.

%%% heap_extract/3

heap_extract(H, _, _) :-
    heap(H, S),
    S =< 0,
    !.

heap_extract(H, K, V) :-
    heap(H, S),
    heap_entry(H, _, K, V),
    heap_has_size(H, 1),
    NewSize is S - 1,
    retract(heap(H, S)),
    assert(heap(H, NewSize)),
    retract(heap_entry(H, _, K, V)),
    !.

heap_extract(H, K, V) :-
    heap(H, _),
    heap_entry(H, _, K, V),
    heap_has_size(H, S),
    heap_head(H, K, V),
    NewSize is S - 1,
    retract(heap(H, S)),
    assert(heap(H, NewSize)),
    retract(heap_entry(H, P, K, V)),
    retract(heap_entry(H, S, K1, V1)),
    assert(heap_entry(H, P, K1, V1)),
    property_maintenance(H, P),
    heapify(H, 1),
    !.

%%% property_maintenance/2

property_maintenance(H, _) :-
    heap(H, _),
    heap_empty(H),
    !.

property_maintenance(H, _) :-
    heap(H, S),
    heap_not_empty(H),
    S = 1,
    !.

property_maintenance(H, Node) :-
    heap(H, S),
    heap_not_empty(H),
    S \= 1,
    Node = 1,
    !.

property_maintenance(H, Node) :-
    heap(H, S),
    heap_not_empty(H),
    S \= 1,
    Node \= 1,
    heap_entry(H, Node, _, _),
    Father is floor(Node / 2),
    heap_entry(H, Father, _, _),
    check_min(H, Node, Father, Minimum),
    Minimum = Father,
    !.

property_maintenance(H, Node) :-
    heap(H, S),
    heap_not_empty(H),
    S \= 1,
    Node \= 1,
    heap_entry(H, Node, KNode, VNode),
    Father is floor(Node / 2),
    heap_entry(H, Father, KFather, VFather),
    check_min(H, Node, Father, Minimum),
    Minimum \= Father,
    swap(H, Node, KNode, VNode, Father, KFather, VFather),
    property_maintenance(H, Father),
    !.

%%% check_min/4

check_min(H, N1, N2, Minimum) :-
    heap(H, S),
    S >= N1,
    S >= N2,
    heap_entry(H, N1, K1, _),
    heap_entry(H, N2, K2, _),
    K1 < K2,
    Minimum is N1,
    !.

check_min(H, N1, N2, Minimum) :-
    heap(H, S),
    S >= N1,
    S >= N2,
    heap_entry(H, N1, K1, _),
    heap_entry(H, N2, K2, _),
    K1 >= K2,
    Minimum is N2,
    !.

%%% check_min/5

check_min(H, N1, N2, N3, Minimum) :-
    heap(H, S),
    S >= N1,
    S >= N2,
    S >= N3,
    check_min(H, N1, N2, Minimum1),
    check_min(H, N2, N3, Minimum2),
    heap_entry(H, Minimum1, K1, _),
    heap_entry(H, Minimum2, K2, _),
    K1 < K2,
    Minimum is Minimum1,
    !.

check_min(H, N1, N2, N3, Minimum) :-
    heap(H, S),
    S >= N1,
    S >= N2,
    S >= N3,
    check_min(H, N1, N2, Minimum1),
    check_min(H, N2, N3, Minimum2),
    heap_entry(H, Minimum1, K1, _),
    heap_entry(H, Minimum2, K2, _),
    K1 >= K2,
    Minimum is Minimum2,
    !.

%%% swap/7

swap(H, P1, K1, V1, P2, K2, V2) :-
    heap_entry(H, P1, K1, V1),
    heap_entry(H, P2, K2, V2),
    retract(heap_entry(H, P1, K1, V1)),
    retract(heap_entry(H, P2, K2, V2)),
    assert(heap_entry(H, P2, K1, V1)),
    assert(heap_entry(H, P1, K2, V2)),
    !.

%%% heapify/2

heapify(H, _) :-
    heap_empty(H),
    !.

heapify(H, _) :-
    heap_not_empty(H),
    heap(H, S),
    S = 1,
    !.

heapify(H, Node) :-
    heap_not_empty(H),
    heap(H, S),
    S < Node,
    !.

heapify(H, Node) :-
    heap(H, S),
    S \= 0,
    S \= 1,
    S >= Node,
    Left is 2 * Node,
    Left > S,
    Right is ((2 * Node) + 1),
    Right > S,
    !.

heapify(H, Node) :-
    heap(H, S),
    S \= 0,
    S \= 1,
    S >= Node,
    Left is 2 * Node,
    S >= Left,
    Right is ((2 * Node) + 1),
    Right > S,
    heap_entry(H, Left, _, _),
    heap_entry(H, Node, _, _),
    check_min(H, Node, Left, Minimum),
    Node = Minimum,
    heapify(H, Left),
    !.

heapify(H, Node) :-
    heap(H, S),
    S \= 0,
    S \= 1,
    S >= Node,
    Left is 2 * Node,
    S >= Left,
    Right is ((2 * Node) + 1),
    Right > S,
    heap_entry(H, Left, _, _),
    heap_entry(H, Node, _, _),
    check_min(H, Node, Left, Minimum),
    Node \= Minimum,
    heap_entry(H, Minimum, KMin, VMin),
    heap_entry(H, Node, KNode, VNode),
    swap(H, Minimum, KMin, VMin, Node, KNode, VNode),
    heapify(H, Minimum),
    !.

heapify(H, Node) :-
    heap(H, S),
    S \= 0,
    S \= 1,
    S >= Node,
    Left is 2 * Node,
    S >= Left,
    Right is ((2 * Node) + 1),
    Right > S,
    heap_entry(H, Left, _, _),
    heap_entry(H, Right, _, _),
    heap_entry(H, Node, _, _),
    check_min(H, Node, Left, Right, Minimum),
    Node = Minimum,
    !.

heapify(H, Node) :-
    heap(H, S),
    S \= 0,
    S \= 1,
    S >= Node,
    Left is 2 * Node,
    S >= Left,
    Right is ((2 * Node) + 1),
    S >= Right,
    heap_entry(H, Left, _, _),
    heap_entry(H, Right, _, _),
    heap_entry(H, Node, _, _),
    check_min(H, Node, Left, Right, Minimum),
    Node \= Minimum,
    heap_entry(H, Minimum, KMin, VMin),
    heap_entry(H, Node, KNode, VNode),
    swap(H, Minimum, KMin, VMin, Node, KNode, VNode),
    heapify(H, Minimum),
    !.

%%% modify_key/4

modify_key(H, NewKey, OldKey, V) :-
    heap(H, _),
    heap_entry(H, _, OldKey, V),
    NewKey \= OldKey,
    retract(heap_entry(H, P, OldKey, V)),
    assert(heap_entry(H, P, NewKey, V)),
    property_maintenance(H, P),
    heapify(H, 1),
    !.

modify_key(H, NewKey, OldKey, V) :-
    heap(H, _),
    heap_entry(H, _, OldKey, V),
    NewKey = OldKey,
    !.

%%% list_heap/1

list_heap(H) :-
    heap(H, _),
    listing(heap_entry(H, _, _, _)),
    !.

%%% MST

%%% mst_prim/2

mst_prim(G, Source) :-
    clean_kb(G),
    graph(G),
    vertex(G, Source),
    new_heap(G),
    graph_vertices(G, Vs),
    initialize(G, Source, Vs),
    prim_cicle(G, Vs),
    delete_heap(G).

clean_kb(G) :-
    retractall(vertex_previous(G, _, _)),
    retractall(vertex_key(G, _, _)),
    !.

initialize(_, _, []) :- !.

initialize(G, Source, Vs) :-
    Vs = [Source | Xs],
    vertex(G, Source),
    assert(vertex_key(G, Source, 0)),
    heap_insert(G, 0, Source),
    initialize(G, Source, Xs),
    !.

initialize(G, Source, Vs) :-
    Vs = [X | Xs],
    vertex(G, X),
    assert(vertex_key(G, X, inf)),
    assert(vertex_previous(G, X, -1)),
    heap_insert(G, inf, X),
    initialize(G, Source, Xs),
    !.

prim_cicle(_, []) :- !.

prim_cicle(G, Vs) :-
    heap_head(G, HK, HV),
    delete(Vs, HV, Xs),
    heap_extract(G, HK, HV),
    adjs(G, HV, Adjs),
    relax(G, HV, Adjs),
    prim_cicle(G, Xs),
    !.

relax(_, _, []) :- !.

relax(G, U, Adjs) :-
    Adjs = [V | Vs],
    V =.. [_, _, Value],
    heap_entry(G, _, K, Value),
    arc(G, Value, U, W),
    vertex_key(G, Value, VKV),
    W < VKV,
    change_previous(G, Value, U),
    change_vertex_key(G, Value, W),
    modify_key(G, W, K, Value),
    relax(G, U, Vs),
    !.

relax(G, U, Adjs) :-
    Adjs = [V | Vs],
    V =.. [_, _, Value],
    heap_entry(G, _, K, Value),
    arc(G, U, Value, W),
    vertex_key(G, Value, VKV),
    W < VKV,
    change_previous(G, Value, U),
    change_vertex_key(G, Value, W),
    modify_key(G, W, K, Value),
    relax(G, U, Vs),
    !.

relax(G, U, Adjs) :-
    Adjs = [_ | Vs],
    relax(G, U, Vs),
    !.

change_previous(G, V, NewPrev) :-
    graph(G),
    vertex(G, V),
    vertex(G, NewPrev),
    retractall(vertex_previous(G, V, _)),
    assert(vertex_previous(G, V, NewPrev)),
    !.

change_vertex_key(G, V, NewKey) :-
    graph(G),
    vertex(G, V),
    retractall(vertex_key(G, V, _)),
    assert(vertex_key(G, V, NewKey)),
    !.

graph_previous(G, Ps) :-
    Previous = vertex_previous(G, _, _),
    findall(Previous, Previous, Ps),
    !.

graph_vertex_key(G, Vks) :-
    VertexK = vertex_key(G, _, _),
    findall(VertexK, VertexK, Vks),
    !.


%%%% end of file -*- mst.pl









