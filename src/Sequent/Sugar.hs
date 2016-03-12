module Sequent.Sugar where

import           Sequent

class ToTerm a where
    toTerm :: a -> Term

instance ToTerm Term where
    toTerm = id

instance ToTerm Variable where
    toTerm = Var

class ToTheorem a where
    toTheorem :: a -> Theorem

instance ToTheorem Theorem where
    toTheorem = id

instance ToTheorem Term where
    toTheorem = TTerm

forall :: (ToTheorem a) => (Term -> a) -> Theorem
forall f = ForAll (toTheorem . f)

forallOf :: (ToTheorem a) => Predicate1 -> (Term -> a) -> Theorem
forallOf p f = forall $ \x -> p <.> x ==> f x

forsome :: (ToTheorem a) => (Term -> a) -> Theorem
forsome f = ForSome (toTheorem . f)

forsomeOf :: (ToTheorem a) => Predicate1 -> (Term -> a) -> Theorem
forsomeOf p f = forsome $ \x -> p <.> x ==> f x

infixr 1 ==>
(==>) :: (ToTheorem a, ToTheorem b) => a -> b -> Theorem
a ==> b = toTheorem a :-> toTheorem b

infixr 0 <==>
(<==>) :: (ToTheorem a, ToTheorem b) => a -> b -> Theorem
a <==> b = a ==> b &&& b ==> a

(<.>) :: ToTerm a => Predicate1 -> a -> Term
f <.> x = App1 f (toTerm x)

(<..>) :: (ToTerm a, ToTerm b) => Predicate2 -> (a, b) -> Term
f <..> (x, y) = App2 f (toTerm x) (toTerm y)

infixr 0 &&&
(&&&) :: (ToTheorem a, ToTheorem b) => a -> b -> Theorem
a &&& b = And (toTheorem a) (toTheorem b)

not' :: (ToTheorem a) => a -> Theorem
not' = Not . toTheorem

rotateLeftAntecedent :: Int -> Proof -> Proof
rotateLeftAntecedent 0 = id
rotateLeftAntecedent n = RotateLeftAntecedent . rotateLeftAntecedent (n - 1)
