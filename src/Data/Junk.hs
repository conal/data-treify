
-- From TReify.hs, line 53, 06/05/2009 12:44:32 PM:

data Bind n where
  Bind :: V a -> n V a -> Bind n

-- From TReify.hs, line 45, 06/05/2009 12:48:14 PM:

-- Hm.  How to get Graph and reifyGraph not have to know about Ty and
-- tyEq?  I'd rather not build in that dependency, since Ty isn't
-- universal.  It handles some types and not others.  Is there a way to
-- fix Ty?  Perhaps an unsafeCoerce hack.  Done!  Now Ty uses TypeRef and
-- an unsafeCoerce.

-- From TReify.hs, line 84, 06/05/2009 01:40:29 PM:

mylookup' st tab =
   do tab2 <- M.lookup (hashStableName st) tab
      Prelude.lookup st tab2

-- From TReify.hs, line 62, 06/05/2009 05:22:13 PM:

-- TODO: Move the following defs to TGraph.hs

type Id = Int

data V a = V Id (Ty a)

-- data Shield2 f g = forall a. Shield2 (f a) (g a)

-- type Bind n = Shield V (n V)

data Bind n = forall a. Bind (V a) (n V a)

data Graph n a = Graph [Bind n] (V a)

-- From TReify.hs, line 23, 06/05/2009 05:25:54 PM:

-- import Data.Reify.TGraph

-- | 'MuRef' is a class that provided a way to reference into a specific type,
-- and a way to map over the deferenced internals.

-- class MuRef a where
--   type DeRef a :: * -> *

--   mapDeRef :: (Applicative m) 
--            => (a -> m          u)
--            -> (a -> m (DeRef a u)

--   -- specialized for use here:
--   mapDeRef :: (a -> IO          Int )
--            -> (a -> IO (DeRef a Int))

