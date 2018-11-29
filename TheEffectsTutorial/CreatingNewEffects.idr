import Effects

data State : Effect where
    Get : State a a (\x => a)
    Put : b -> State () a (\x => b)

STATE : Type -> EFFECT
STATE t = MkEff t State

Handler State m where
    handle s Get k = k s s
    handle _ (Put s') k = k () s'

get : Eff s [STATE s]
get = call Get

put : a -> Eff () [STATE a]
put s = call (Put s)

putM : b -> Eff () [STATE a] [STATE b]
putM s = call (Put s)

