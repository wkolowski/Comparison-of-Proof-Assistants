module Quicksort

open FStar.All

noeq type qsArgs 'a =
{
    short :
        l : list 'a -> option (h : 'a * t : list 'a{len t < len l});
    adhoc :
        l : list 'a -> sorted : list 'a;
    choosePivot :
        'a -> l : list 'a -> pivot : 'a *
                             rest : list 'a{len rest = len l};
    partition :
        'a -> l : list 'a -> lt : list 'a{len lt < len l} *
                             eq : list 'a *
                             gt : list 'a{len gt < len l};
}

let rec qs
    (args : qsArgs 'a) (l : list 'a)
    : Tot (list 'a) (decreases (len l))
    =
    match args.short l with
    | None        -> args.adhoc l
    | Some (h, t) ->
        match args.choosePivot h t with
        | (pivot, rest) ->
            match args.partition pivot rest with
            | (lt, eq, gt) ->
                app (qs args lt) (pivot :: app eq (qs args gt))
