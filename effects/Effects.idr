module Effects

import Language.Reflection
import public Effect.Default
import Data.Vect
import Control.Monad.State

--- Effectful computations are described as algebraic data types that
--- explain how an effect is interpreted in some underlying context.

%access public
-- ----------------------------------------------------------------- [ Effects ]
||| The Effect type describes effectful computations.
|||
||| This type is parameterised by:
||| + The input resource.
||| + The return type of the computation.
||| + The computation to run on the resource.
Effect : Type
Effect = (x : Type) -> Type -> (x -> Type) -> Type

||| The `EFFECT` Data type describes how to promote the Effect
||| description into a concrete effect.
%error_reverse
data EFFECT : Type where
     MkEff     : Type -> Effect -> EFFECT

||| Handler classes describe how an effect `e` is translated to the
||| underlying computation context `m` for execution.
class Handler (e : Effect) (m : Type -> Type) where
  ||| How to handle the effect.
  |||
  ||| @ r The resource being handled.
  ||| @ eff The effect to be applied.
  ||| @ k The continuation to pass the result of the effect
  covering handle : (r : res) -> (eff : e t res resk) ->
                    (k : ((x : t) -> resk x -> m a)) -> m a

||| Get the resource type (handy at the REPL to find out about an effect)
resourceType : EFFECT -> Type
resourceType (MkEff t e) = t

-- --------------------------------------- [ Properties and Proof Construction ]
data SubList : List a -> List a -> Type where
     SubNil : SubList [] []
     Keep   : SubList xs ys -> SubList (x :: xs) (x :: ys)
     Drop   : SubList xs ys -> SubList xs (x :: ys)

subListId : SubList xs xs
subListId {xs = Nil} = SubNil
subListId {xs = x :: xs} = Keep subListId

infixr 5 :!

namespace Env
  data Env  : (m : Type -> Type) -> List EFFECT -> Type where
       Nil  : Env m Nil
       (::) : Handler eff m => a -> Env m xs -> Env m (MkEff a eff :: xs)

data EffElem : Effect -> Type ->
               List EFFECT -> Type where
     Here : EffElem x a (MkEff a x :: xs)
     There : EffElem x a xs -> EffElem x a (y :: xs)

getEff : (xs : List EFFECT) -> EffElem e a xs -> EFFECT
getEff (e@(MkEff a x) :: ys) Here = e 
getEff (y :: ys) (There x) = getEff ys x

||| make an environment corresponding to a sub-list
dropEnv : Env m ys -> SubList xs ys -> Env m xs
dropEnv [] SubNil = []
dropEnv (v :: vs) (Keep rest) = v :: dropEnv vs rest
dropEnv (v :: vs) (Drop rest) = dropEnv vs rest

updateWith : (ys' : List a) -> (xs : List a) ->
             SubList ys xs -> List a
updateWith (y :: ys) (x :: xs) (Keep rest) = y :: updateWith ys xs rest
updateWith ys        (x :: xs) (Drop rest) = x :: updateWith ys xs rest
updateWith []        []        SubNil      = []
updateWith (y :: ys) []        SubNil      = y :: ys
updateWith []        (x :: xs) (Keep rest) = []

||| Put things back, replacing old with new in the sub-environment
rebuildEnv : Env m ys' -> (prf : SubList ys xs) ->
             Env m xs -> Env m (updateWith ys' xs prf)
rebuildEnv []        SubNil      env = env
rebuildEnv (x :: xs) SubNil      env = x :: xs
rebuildEnv []        (Keep rest) (y :: env) = []
rebuildEnv (x :: xs) (Keep rest) (y :: env) = x :: rebuildEnv xs rest env
rebuildEnv xs        (Drop rest) (y :: env) = y :: rebuildEnv xs rest env


-- -------------------------------------------------- [ The Effect EDSL itself ]

updateResTy : (val : t) ->
              (xs : List EFFECT) -> EffElem e a xs -> e t a b ->
              List EFFECT
updateResTy {b} val (MkEff a e :: xs) Here n = (MkEff (b val) e) :: xs
updateResTy     val (x :: xs)    (There p) n = x :: updateResTy val xs p n

infix 5 :::, :-, :=

data LRes : lbl -> Type -> Type where
     (:=) : (x : lbl) -> res -> LRes x res

(:::) : lbl -> EFFECT -> EFFECT
(:::) {lbl} x (MkEff r e) = MkEff (LRes x r) e

using (lbl : Type)
  instance Default a => Default (LRes lbl a) where
    default = lbl := default

private
unlabel : {l : ty} -> Env m [l ::: x] -> Env m [x]
unlabel {m} {x = MkEff a eff} [l := v] = [v]

private
relabel : (l : ty) -> Env m xs -> Env m (map (\x => l ::: x) xs)
relabel {xs = []} l [] = []
relabel {xs = (MkEff a e :: xs)} l (v :: vs) = (l := v) :: relabel l vs

-- ------------------------------------------------- [ The Language of Effects ]

-- class NewEffect (e : Effect) a b where
--   new :  

||| Definition of a language of effectful programs.
|||
||| @ x The return type of the result.
||| @ es The list of allowed side-effects.
||| @ ce Function to compute a new list of allowed side-effects.
data EffT : (m : Type -> Type) -> 
            (x : Type)
            -> (es : List EFFECT)
            -> (ce : x -> List EFFECT) -> Type where
     value    : (val : a) -> EffT m a (xs val) xs
     ebind    : EffT m a xs xs' ->
                ((val : a) -> EffT m b (xs' val) xs'') -> EffT m b xs xs''
     callP    : (prf : EffElem e a xs) ->
                (eff : e t a b) ->
                EffT m t xs (\v => updateResTy v xs prf eff)

     liftP    : (prf : SubList ys xs) ->
                EffT m t ys ys' -> 
                EffT m t xs (\v => updateWith (ys' v) xs prf)

     rec      : Inf (EffT m t xs xs') -> EffT m t xs xs'

     (:-)     : (l : ty) ->
                EffT m t [x] xs' -> -- [x] (\v => xs) ->
                EffT m t [l ::: x] (\v => map (l :::) (xs' v))

Eff : (x : Type) -> (es : List EFFECT) -> (ce : x -> List EFFECT) -> Type
Eff x es ce = {m : Type -> Type} -> EffT m x es ce

%no_implicit
(>>=)   : EffT m a xs xs' ->
          ((val : a) -> EffT m b (xs' val) xs'') -> EffT m b xs xs''
(>>=) = ebind

-- namespace SimpleBind
--   (>>=) : Eff m a xs (\v => xs) ->
--           ((val : a) -> Eff m b xs xs') -> Eff m b xs xs'
--   (>>=) = ebind

||| Run a subprogram which results in an effect state the same as the input.
staticEff : EffT m a xs (\v => xs) -> EffT m a xs (\v => xs)
staticEff = id

||| Explicitly give the expected set of result effects for an effectful
||| operation.
toEff : .(xs' : List EFFECT) -> EffT m a xs (\v => xs') -> EffT m a xs (\v => xs')
toEff xs' = id

return : a -> EffT m a xs (\v => xs)
return x = value x

-- ------------------------------------------------------ [ for idiom brackets ]

infixl 2 <*>

pure : a -> EffT m a xs (\v => xs)
pure = value

pureM : (val : a) -> EffT m a (xs val) xs
pureM = value

(<*>) : EffT m (a -> b) xs (\v => xs) ->
        EffT m a xs (\v => xs) -> EffT m b xs (\v => xs)
(<*>) prog v = do fn <- prog
                  arg <- v
                  return (fn arg)

-- ---------------------------------------------------------- [ an interpreter ]

private
execEff : Env m xs -> (p : EffElem e res xs) ->
          (eff : e a res resk) ->
          ((v : a) -> Env m (updateResTy v xs p eff) -> m t) -> m t
execEff (val :: env) Here eff' k
    = handle val eff' (\v, res => k v (res :: env))
-- FIXME: Teach the elaborator to propagate parameters here
execEff {e} {a} {res} {resk} (val :: env) (There p) eff k
    = execEff {e} {a} {res} {resk} env p eff (\v, env' => k v (val :: env'))

-- Q: Instead of m b, implement as StateT (Env m xs') m b, so that state
-- updates can be propagated even through failing computations?

eff : Env m xs -> EffT m a xs xs' -> 
      ((x : a) -> Env m (xs' x) -> m b) -> m b
eff env (value x) k = k x env
eff env (prog `ebind` c) k
   = eff env prog (\p', env' => eff env' (c p') k)
eff env (callP prf effP) k = execEff env prf effP k
eff env (liftP prf effP) k
   = let env' = dropEnv env prf in
         eff env' effP (\p', envk => k p' (rebuildEnv envk prf env))
-- FIXME:
-- xs is needed explicitly because otherwise the pattern binding for
-- 'l' appears too late. Solution seems to be to reorder patterns at the
-- end so that everything is in scope when it needs to be.
eff {xs = [l ::: x]} env (l :- prog) k
   = let env' = unlabel env in
         eff env' prog (\p', envk => k p' (relabel l envk))

-- yuck :) Haven't got type class instances working nicely in tactic
-- proofs yet, and 'search' can't be told about any hints yet,
-- so just brute force it.
syntax MkDefaultEnv = with Env
                       (| [], [default], [default, default],
                          [default, default, default],
                          [default, default, default, default],
                          [default, default, default, default, default],
                          [default, default, default, default, default, default],
                          [default, default, default, default, default, default, default],
                          [default, default, default, default, default, default, default, default] |)

call : {a, b: _} -> {e : Effect} ->
       (eff : e t a b) ->
       {default tactics { search 100; }
          prf : EffElem e a xs} ->
      EffT m t xs (\v => updateResTy v xs prf eff)
call e {prf} = callP prf e

implicit
lift : EffT m t ys ys' ->
       {default tactics { search 100; }
          prf : SubList ys xs} ->
       EffT m t xs (\v => updateWith (ys' v) xs prf)
lift e {prf} = liftP prf e


-- --------------------------------------------------------- [ Running Effects ]
||| Run an effectful program.
|||
||| The content (`m`) in which to run the program is taken from the
||| environment in which the program is called. The `env` argument is
||| implicit and initialised automatically.
|||
||| @prog The effectful program to run.
run : Applicative m => {default MkDefaultEnv env : Env m xs}
    -> (prog : EffT m a xs xs') -> m a
run {env} prog = eff env prog (\r, env => pure r)

||| Run an effectful program in the identity context.
|||
||| A helper function useful for when the given context is 'pure'.
||| The `env` argument is implicit and initialised automatically.
|||
||| @prog The effectful program to run.
runPure : {default MkDefaultEnv env : Env id xs} -> (prog : EffT id a xs xs') -> a
runPure {env} prog = eff env prog (\r, env => r)

||| Run an effectful program in a given context `m` with a default value for the environment.
|||
||| This is useful for when there is no default environment for the given context.
|||
||| @env The environment to use.
||| @prog The effectful program to run.
runInit : Applicative m => (env : Env m xs) -> (prog : EffT m a xs xs') -> m a
runInit env prog = eff env prog (\r, env => pure r)

||| Run an effectful program with a given default value for the environment.
|||
||| A helper function useful for when the given context is 'pure' and there is no default environment.
|||
||| @env The environment to use.
||| @prog The effectful program to run.
runPureInit : (env : Env id xs) -> (prog : EffT id a xs xs') -> a
runPureInit env prog = eff env prog (\r, env => r)

runWith : (a -> m a) -> Env m xs -> EffT m a xs xs' -> m a
runWith inj env prog = eff env prog (\r, env => inj r)

runEnv : Applicative m => Env m xs -> EffT m a xs xs' ->
         m (x : a ** Env m (xs' x))
runEnv env prog = eff env prog (\r, env => pure (r ** env))

-- ------------------------------------------------------------ [ Notation ]

infix 5 :=>

-- 'sig' gives the signature for an effect. There are three versions
-- depending on whether there is no state change, a non-dependent change,
-- or a dependent change. These are easily disambiguated by type.

namespace NoResourceEffect
  sig : Effect -> Type -> Type
  sig e r = e r () (\v => ())

namespace NoUpdateEffect
  sig : Effect -> (ret : Type) -> (resource : Type) -> Type
  sig e r e_in = e r e_in (\v => e_in)

namespace UpdateEffect
  sig : Effect -> (ret : Type) -> (res_in : Type) -> (res_out : Type) -> Type
  sig e r e_in e_out = e r e_in (\v => e_out)

namespace DepUpdateEffect
  sig : Effect -> 
        (ret : Type) -> (res_in : Type) -> (res_out : ret -> Type) -> Type
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

EffsT : (m : Type -> Type) -> (x : Type) -> List (EffTrans x) -> Type
EffsT m x xs = EffT m x (proto_in xs) (\val : x => proto_out xs val)
  where
    proto_out : List (EffTrans x) -> x -> List EFFECT
    proto_out [] val = []
    proto_out ((e_in :=> e_out) :: xs) val 
        = let rec = proto_out xs val in e_out val :: rec 

    proto_in : List (EffTrans x) -> List EFFECT
    proto_in [] = []
    proto_in ((e_in :=> e_out) :: xs) 
        = let rec = proto_in xs in e_in :: rec 

Effs : (x : Type) -> List (EffTrans x) -> Type
Effs x xs = {m : Type -> Type} -> EffsT m x xs

-- ----------------------------------------------- [ some higher order things ]

-- mapE : (a -> EffsT m b xs) -> List a -> EffsT m (List b) xs
-- mapE f []        = pure []
-- mapE f (x :: xs) = [| f x :: mapE f xs |]
-- 
-- 
-- mapVE : (a -> EffsT m b xs) ->
--         Vect n a ->
--         EffsT m (Vect n b) xs
-- mapVE f []        = pure []
-- mapVE f (x :: xs) = [| f x :: mapVE f xs |]

-- when : Bool -> Lazy (EffsT m () xs) -> EffsT m () xs
-- when True  e = Force e
-- when False e = pure ()

