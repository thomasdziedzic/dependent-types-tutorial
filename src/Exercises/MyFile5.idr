module Exercises.MyFile5

import Data.Fin
import Data.Vect
import Data.List.Elem

%default total

record Fix (f : Type -> Type)  where
  constructor Rec
  unFix : Lazy (f (Fix f))

namespace Application
  data CFT : Nat -> Type where
    Var : Fin n -> CFT n
    Zero : CFT n
    One  : CFT n
    Plus : CFT n -> CFT n -> CFT n
    Times : CFT n -> CFT n -> CFT n
    Mu : CFT (S n) -> CFT n
    Apply : CFT (S n) -> CFT n -> CFT n

  MaybeDesc : CFT 1
  MaybeDesc = Plus One (Var 0)

  BoolDesc : CFT 0
  BoolDesc = Plus One One

  MaybeBool: CFT 0
  MaybeBool = Apply MaybeDesc BoolDesc

  ToType : CFT n -> Vect n Type  -> Type
  ToType (Var x) xs = index x xs
  ToType Zero xs = Void
  ToType One xs = Unit
  ToType (Plus x y) xs = Either (ToType x xs) (ToType y xs)
  ToType (Times x y) xs = Pair (ToType x xs) (ToType y xs)
  ToType (Mu x) xs = Fix (ToType x . (:: xs))
  ToType (Apply x y) xs =
    let arg = ToType y xs
    in ToType x (arg :: xs)

  ListDesc : CFT 1
  ListDesc = Mu (Plus One (Times (Var 1) (Var 0)))

  ListType : Type -> Type
  ListType x = ToType ListDesc [x]

  NatDesc : CFT 0
  NatDesc = Apply ListDesc One

  NatType : Type
  NatType = ToType NatDesc []

  ListNil : ListType a
  ListNil = Rec $ Left ()

  ListCons : a -> ListType a -> ListType a
  ListCons x y = Rec $ Right (x, y)

  NatZero : NatType
  NatZero = Rec $ Left ()

  NatSucc : NatType -> NatType
  NatSucc x = Rec $ Right ((), x)

  BoolOneDesc : CFT 0
  BoolOneDesc = Apply MaybeDesc One

  BoolOneType : Type
  BoolOneType = ToType BoolOneDesc []

  BoolOneTrue : BoolOneType
  BoolOneTrue = Left ()

  BoolOneFalse : BoolOneType
  BoolOneFalse = Right ()

  EitherDesc : CFT 2
  EitherDesc = (Var 0) `Plus` (Var 1)

  EitherType : Type -> Type -> Type
  EitherType l r = ToType EitherDesc [l, r]

  EitherLeft : l -> EitherType l r
  EitherLeft = Left

  EitherRight : r -> EitherType l r
  EitherRight = Right

  MaybeEitherDesc : CFT 1
  MaybeEitherDesc =  Apply EitherDesc One

  MaybeEitherType : Type -> Type
  MaybeEitherType x = ToType MaybeEitherDesc [x]

  MaybeEitherNothing : MaybeEitherType a
  MaybeEitherNothing = Left ()

  MaybeEitherJust : a -> MaybeEitherType a
  MaybeEitherJust x = Right x

  UnitListDesc : CFT 0
  UnitListDesc = Apply ListDesc Zero

  UnitListType : Type
  UnitListType = ToType UnitListDesc []

  UnitList : UnitListType
  UnitList = Rec $ Left ()

infixr 1 =>>

data Kind : Type where
  Plain : Kind
  (=>>) : Kind -> Kind -> Kind

Context : Type
Context = List Kind

data TyC : (0 _ : Context) -> (0 _ : Kind) -> Type where
  -- a type variable, it has kind `e`
  Var : e `Elem` ctx -> TyC ctx e

  -- Zero and One are plain types
  Zero : TyC ctx Plain
  One  : TyC ctx Plain

  -- Times only works on plain types
  Times : TyC ctx Plain
       -> TyC ctx Plain
       -> TyC ctx Plain

  -- Plus only works on plain types
  Plus : TyC ctx Plain
      -> TyC ctx Plain
      -> TyC ctx Plain

  -- Mu has kind `a`
  Mu : TyC (a :: ctx) a
    -> TyC       ctx a

  -- Type application
  App : {a : _}
     -> TyC ctx (a =>> b)
     -> TyC ctx a
     -> TyC ctx b

  -- lambda abstraction
  Lam : TyC (a :: ctx) b
      ------------------
     -> TyC ctx (a =>> b)

EitherDesc : TyC (Plain :: Plain :: ctx) Plain
EitherDesc = Plus (Var Here) (Var (There Here))

EitherLam : TyC ctx (Plain =>> Plain =>> Plain)
EitherLam = Lam (Lam EitherDesc)

MaybeDesc : TyC ctx (Plain =>> Plain)
MaybeDesc = App EitherLam One

ListDesc : TyC (Plain :: ctx) Plain
ListDesc = Mu (Plus One (Times (Var (There Here)) (Var Here)))

Identity : TyC [n] n
Identity = Var Here

AppIdMaybe : TyC [] (Plain =>> Plain)
AppIdMaybe = App (Lam Identity) MaybeDesc

ListEitherDesc : TyC ctx (Plain =>> Plain =>> Plain)
ListEitherDesc = Lam (Lam (App (Lam ListDesc) EitherDesc))
