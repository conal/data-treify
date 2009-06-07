{-# LANGUAGE GADTs, KindSignatures, TypeOperators, PatternGuards
           , ScopedTypeVariables, TypeFamilies, FlexibleInstances, CPP
  #-}
{-# OPTIONS_GHC -Wall -fno-warn-missing-methods -fno-warn-missing-signatures #-}

-- This version uses Data.Ty

module Exp where

import Control.Applicative (pure,(<$>),(<*>))
import qualified Data.IntMap as I
import Data.Maybe (fromMaybe) -- ,fromJust
import Data.Typeable

import Data.Proof.EQ
import Data.Ty
import Data.TReify

-- #include "Typeable.h"

{--------------------------------------------------------------------
    Expressions
--------------------------------------------------------------------}

data Op :: * -> * where
  Add :: Num a  => Op (a -> a -> a)
  Mul :: Num a  => Op (a -> a -> a)
  Lit :: Show a => a -> Op a

instance ShowF Op where
  showF Add = "Add"
  showF Mul = "Mul"
  showF (Lit a) = show a

instance Show (Op a) where show = showF

-- Expressions, parameterized by variable type (constructor) and
-- expression type.
data E :: (* -> *) -> * -> * where
  Op   :: Op a -> E v a
  (:^) :: Typeable a =>
          E v (a -> b) -> E v a -> E v b
  Let  :: v a -> E v a -> E v b -> E v b
  Var  :: v a -> E v a

data N :: (* -> *) -> * -> * where
  ON  :: Op a -> N v a
  App :: Typeable a =>
         v (a -> b) -> v a -> N v b

instance ShowF v => ShowF (N v) where
  showF (ON o)    = unwords ["ON" ,showF o]
  showF (App a b) = unwords ["App",showF a,showF b]

instance Show (E V a) where
  show (Op o) = show o
  show (u :^ v) = parens $ unwords [show u,show v]
  show (Let v a b) = unwords ["let",show v,"=",show a,"in",show b]
  show (Var v) = show v


parens :: String -> String
parens = ("(" ++) . (++ ")")


-- These Typeable instances don't work, because the first parameter to E
-- and N is higher-kinded.

-- INSTANCE_TYPEABLE2(N,nodeTc,"N")
-- INSTANCE_TYPEABLE2(E,expTC ,"E")


instance MuRef (E v) where
  type DeRef (E v)    = N
  mapDeRef _ (Op o)   = pure $ ON o
  mapDeRef f (a :^ b) = App <$> f a <*> f b
  mapDeRef _ Let{}    = notSupp "Let"
  mapDeRef _ Var{}    = notSupp "Var"

notSupp :: String -> a
notSupp meth = error $ "mapDeRef on E: "++meth++" not supported"

-- TODO: Consider splitting Let/Var off from E.  Then E wouldn't need the
-- v parameter.
-- I could use N and Mu to define an E without Let & Var and then use a
-- standard MuRef instance and a standard extension to include Let & Var.
-- Wouldn't be as convenient for simplification rules, because of the
-- explicit Mu constructors.  Consider it, however, since it makes a
-- simple type distinction between the input to CSE and the output.  Oh,
-- and I could have different ways to embed Let.  For C-like languages, I
-- could restrict the lets to be on the outside (odd for conditionals,
-- though).


nodeE :: N v a -> E v a
nodeE (ON o)    = Op o
nodeE (App u v) = Var u :^ Var v

unGraph :: Graph N a -> E V a
unGraph (Graph binds root) =
  foldr (\ (Bind v n) -> Let v (nodeE n)) (Var root) (reverse binds)


-- Convert expressions to simple SSA form
ssa :: Typeable a => E V a -> IO (E V a)
ssa = fmap unGraph . reifyGraph



children :: N V a -> [Id]
children (ON  _)   = []
children (App (V a _) (V b _)) = [a,b]

childrenB :: Bind N -> [Id]
childrenB (Bind _ n) = children n


-- Number of references for each node.  Important: partially apply, so
-- that the binding list can be converted just once into an efficiently
-- searchable representation.
uses :: [Bind N] -> (Id -> Int)
uses = fmap (fromMaybe 0) .
       flip I.lookup .
       histogram .
       concatMap childrenB

-- histogram :: Ord k => [k] -> I.Map k Int
-- histogram = foldr (\ k -> I.insertWith (+) k 1) I.empty

histogram :: [Int] -> I.IntMap Int
histogram = foldr (\ k -> I.insertWith (+) k 1) I.empty

-- bindsF :: [Bind v] -> (Ty a -> v a -> N v a)
-- bindsF = undefined

-- Slow version
bindsF' :: [Bind N] -> (V a -> N V a)
bindsF' [] _ = error "bindsF: ran out of bindings"
bindsF' (Bind (V i a) n : binds') v@(V i' a')
  | Just Refl <- a `tyEq` a', i == i' = n
  | otherwise                         = bindsF' binds' v

-- Fast version, using an IntMap.  Important: partially apply.
bindsF :: forall n a. [Bind n] -> (V a -> n V a)
bindsF binds = \ (V i' a') -> extract a' (I.lookup i' m)
 where
   m :: I.IntMap (Bind n)
   m = I.fromList [(i,b) | b@(Bind (V i _) _) <- binds]
   extract :: Ty a' -> Maybe (Bind n) -> n V a'
   extract _ Nothing            = error "bindsF: variable not found"
   extract a' (Just (Bind (V _ a) n))
     | Just Refl <- a `tyEq` a' = n
     | otherwise                = error "bindsF: wrong type"

unGraph2 :: Graph N a -> E V a
unGraph2 (Graph binds root) = foldr llet (var' root) (reverse binds)
 where
   -- Wrap a let if non-trivial
   llet :: Bind N -> E V b -> E V b
   llet bind | trivial bind = id
   llet (Bind v n) = Let v (nodeE' n)
   -- How many uses of variable
   count :: Id -> Int
   count = uses binds
   -- Bindings as IntMap lookup
   psf :: V a -> N V a
   psf = bindsF binds
   -- Too trivial to bother abstracting.
   trivial :: Bind N -> Bool
   trivial (Bind _ (ON _))                = True
   trivial (Bind (V i _) _) | count i < 2 = True
   trivial _                              = False
   -- Like nodeE but with inlining of trivial bindings
   nodeE' :: N V a -> E V a
   nodeE' (ON o)    = Op o
   nodeE' (App a b) = var' a :^ var' b
   -- Variable reference or inline
   var' :: V a -> E V a
   var' v | trivial (Bind v n) = nodeE' n
          | otherwise          = Var v
    where
      n = psf v

-- TODO: generalize unGraph2 from V.

-- | Common subexpression elimination
cse :: Typeable a => E V a -> IO (E V a)
cse = fmap unGraph2 . reifyGraph


{--------------------------------------------------------------------
    Utilities for convenient expression building
--------------------------------------------------------------------}

op2 :: (Typeable a, Typeable b, Typeable c) =>
       Op (a -> b -> c) -> E v a -> E v b -> E v c
op2 h a b = Op h :^ a :^ b

instance Eq (E v a)

instance (Typeable a, Num a) => Num (E V a) where
  fromInteger x = Op (Lit (fromInteger x))
  (+) = op2 Add
  (*) = op2 Mul

sqr :: Num a => a -> a
sqr x = x * x

{--------------------------------------------------------------------
    Testing
--------------------------------------------------------------------}

-- test expressions
e1 = 3 + 5 :: E V Integer
e2 = e1 * e1
e3 = 3 + 3 :: E V Integer

test :: Int -> E V Integer
test n = iterate sqr e1 !! n

-- test reifications
g1 = reifyGraph e1
g2 = reifyGraph e2
g3 = reifyGraph e3

gtest = reifyGraph . test

g4 = test 5

-- *TEReify> g4
-- let [(1,App 2 4),(2,App 3 4),(4,App 5 7),(5,App 6 7),(7,App 8 10),(8,App 9 10),(10,App 11 13),(11,App 12 13),(13,App 14 16),(14,App 15 16),(16,App 17 20),(20,Lit 5),(17,App 18 19),(19,Lit 3),(18,Lit Add),(15,Lit Mul),(12,Lit Mul),(9,Lit Mul),(6,Lit Mul),(3,Lit Mul)] in 1

e5 = e1 ^ (29 :: Integer)
g5 = reifyGraph e5

-- *TEReify> g5
-- let [(21,App 22 41),(41,App 42 44),(44,App 45 36),(45,App 46 30),(46,Lit Mul),(42,App 43 27),(43,Lit Mul),(22,App 23 24),(24,App 25 27),(25,App 26 27),(27,App 28 30),(28,App 29 30),(30,App 31 33),(31,App 32 33),(33,App 34 36),(34,App 35 36),(36,App 37 40),(40,Lit 5),(37,App 38 39),(39,Lit 3),(38,Lit Add),(35,Lit Mul),(32,Lit Mul),(29,Lit Mul),(26,Lit Mul),(23,Lit Mul)] in 21


