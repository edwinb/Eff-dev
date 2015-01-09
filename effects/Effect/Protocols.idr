module Effect.Protocols

-- Helpers for writing and using effects that implement protocols with
-- state transitions

import public Effects

infix 5 :=>

-- 'sig' gives the signature for an effect. There are three versions
-- depending on whether there is no state change, a non-dependent change,
-- or a dependent change. These are easily disambiguated by type.

namespace NoResourceEffect
  sig : Effect -> Type -> Type
  sig e r = e r () (\v => ())

namespace NoUpdateEffect
  sig : Effect -> Type -> Type -> Type
  sig e r e_in = e r e_in (\v => e_in)

namespace UpdateEffect
  sig : Effect -> Type -> Type -> Type -> Type
  sig e r e_in e_out = e r e_in (\v => e_out)

namespace DepUpdateEffect
  sig : Effect -> (x : Type) -> Type -> (x -> Type) -> Type
  sig e r e_in e_out = e r e_in e_out


-- a single effect transition.

data EffTrans : Type -> Type where
     (:=>) : EFFECT -> (x -> EFFECT) -> EffTrans x

-- 'trans' gives a single effect transition. Again three versions, for
-- no transition, non-dependent transition and dependent transition, again
-- disambiguated by type, but the one with no update can be implicit.

namespace NoUpdateTrans
  implicit
  trans : EFFECT -> EffTrans x
  trans t = t :=> (\v => t)

namespace UpdateTrans
  trans : EFFECT -> EFFECT -> EffTrans x
  trans s t = s :=> (\v => t)

namespace DepUpdateTrans
  trans : EFFECT -> (x -> EFFECT) -> EffTrans x
  trans s t = s :=> t

Proto : (x : Type) -> List (EffTrans x) -> Type
Proto x xs = Eff x (proto_in xs) (\val : x => proto_out xs val)
  where
    proto_out : List (EffTrans x) -> x -> List EFFECT
    proto_out [] val = []
    proto_out ((e_in :=> e_out) :: xs) val 
        = let rec = proto_out xs val in e_out val :: rec 

    proto_in : List (EffTrans x) -> List EFFECT
    proto_in [] = []
    proto_in ((e_in :=> e_out) :: xs) 
        = let rec = proto_in xs in e_in :: rec 

