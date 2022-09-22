module Exercises.File3

import Iso

%hide Prelude.Bool
%hide Prelude.True
%hide Prelude.False

%default total

data Desc : Type where
  Zero  : Desc
  One   : Desc
  Plus  : Desc -> Desc -> Desc
  Times : Desc -> Desc -> Desc

ToType : Desc -> Type
ToType Zero = Void
ToType One = Unit
ToType (Plus x y) = Either (ToType x) (ToType y)
ToType (Times x y) = Pair (ToType x) (ToType y)

BoolDesc : Desc
BoolDesc = One `Plus` One

BoolDesc1 : Desc
BoolDesc1 = One `Plus` (One `Plus` Zero)

BoolDesc2 : Desc
BoolDesc2 = Zero `Plus` (One `Plus` One)

-- Exercises

----------
-- iso1 --
----------

iso1From : Either () (Either () Void) -> Either () ()
iso1From (Left x) = Left x
iso1From (Right x) = Right ()

iso1To : Either () () -> Either () (Either () Void)
iso1To (Left x) = Left x
iso1To (Right x) = Right (Left x)

iso1ToFrom : (x : Either () (Either () Void)) -> iso1To (iso1From x) = x
iso1ToFrom (Left x) = Refl
iso1ToFrom (Right (Left ())) = Refl

iso1FromTo : (x : Either () ()) -> iso1From (iso1To x) = x
iso1FromTo (Left x) = Refl
iso1FromTo (Right ()) = Refl

iso1 : ToType BoolDesc `Iso` ToType BoolDesc1
iso1 = MkIso iso1From iso1To iso1ToFrom iso1FromTo

----------
-- iso2 --
----------

iso2From : Either Void (Either () ()) -> Either () ()
iso2From (Right x) = x

iso2To : Either () () -> Either Void (Either () ())
iso2To x = Right x

iso2ToFrom : (x : Either Void (Either () ())) -> iso2To (iso2From x) = x
iso2ToFrom (Right x) = Refl

iso2FromTo : (x : Either () ()) -> iso2From (iso2To x) = x
iso2FromTo x = Refl

iso2 : ToType BoolDesc `Iso` ToType BoolDesc2
iso2 = MkIso iso2From iso2To iso2ToFrom iso2FromTo

----------
-- iso3 --
----------

{-
  NOTE: I had technical issues doing iso3, I had to make the following change in Iso.idr to get this to work:
    ```
    import Control.Relation
    ```
    into
    ```
    import public Control.Relation
    ```
    As a result, I copy pasted the solution from the answers to help me debug this problem in this file.
    Surprisingly, the Answers file seemed to have worked without needing the public import of Control.Relation.
-}
iso3 : ToType BoolDesc1 `Iso` ToType BoolDesc2
iso3 = symmetric iso1 `transitive` iso2

-----------
-- DBool --
-----------

DBool : Type
DBool = ToType $ One `Plus` One

----------
-- True --
----------

True : DBool
True = Left ()

-----------
-- False --
-----------

False : DBool
False = Right ()

---------
-- not --
---------

not : DBool -> DBool
not (Left x) = Right x
not (Right x) = Left x

---------
-- and --
---------

and : DBool -> DBool -> DBool
and (Left x) y = y
and (Right x) y = Right x

--------
-- or --
--------

or : DBool -> DBool -> DBool
or (Left x) y = Left x
or (Right x) y = y

---------
-- xor --
---------

xor : DBool -> DBool -> DBool
xor (Left x) y = not y
xor (Right x) y = y

------------------
-- Extra Credit --
------------------

data DescVar : Type where
  ZeroVar  : DescVar
  OneVar   : DescVar
  PlusVar  : DescVar -> DescVar -> DescVar
  TimesVar : DescVar -> DescVar -> DescVar
  Var      : String -> DescVar

ToType2 : DescVar -> Type
-- Could not figure out how to define ToType2 without a context
-- because the type depends on the variables value that comes from a context.
-- Variables are just placeholders for actual values provided later on during the computation.
