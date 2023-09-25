module PrefixTrace where

import Prelude hiding (lookup, log)
import Expr
import Template
import Control.Monad.Fix
import Later
import Data.Functor.Identity
import Control.Monad.Trans.Writer

type Evt f = forall v. f v -> f v

data PrefixTrace f v = Step (Evt f) (Later (PrefixTrace f v)) | Ret !v | Stuck
  deriving (Functor)

instance Applicative (PrefixTrace f) where
  pure = Ret
  Step s f <*> a = Step s (fmap (<*> a) f)
  Stuck <*> _ = Stuck
  f <*> Step s a = Step s (fmap (f <*>) a)
  _ <*> Stuck = Stuck
  Ret f <*> Ret a = Ret (f a)

instance Monad (PrefixTrace f) where
  Stuck >>= _ = Stuck
  Step s d >>= k = Step s (fmap (>>= k) d)
  Ret a >>= k = k a

instance MonadFix (PrefixTrace f) where
  mfix f = trc
    where
      (trc,v) = go (f v)
      go (Step s t) = (Step s (pure t'), v)
        where
          (t', v) = go (t unsafeTick)
      go (Ret v) = (Ret v, v)
      go Stuck = (Stuck, undefined)

instance MonadTrace Identity m => MonadTrace Later (PrefixTrace m) where
  stuck = Stuck
  lookup x = Step (lookup x . Identity)
  app1 = Step app1 . pure
  app2 = Step app2 . pure
  bind = Step bind . pure
  case1 = Step case1 . pure
  case2 = Step case2 . pure
  update = Step update . pure
  let_ = Step let_ . pure

instance MonadRecord (PrefixTrace m) where
  recordIfJust (Ret Nothing) = Nothing
  recordIfJust (Ret (Just a)) = Just (Ret a)
  recordIfJust Stuck = Just Stuck
  recordIfJust (Step f s) = Step f . pure <$> (recordIfJust (s unsafeTick)) -- wildly unproductive! This is the culprit of Clairvoyant CbV

-- | Potentitally infinite list; use take on result
getPrefixTraces :: MonadTrace Identity m => Int -> PrefixTrace m v -> [m ()]
getPrefixTraces n s = return () : case s of
  Step f s' | n > 0 -> map f (getPrefixTraces (n-1) (s' unsafeTick))
  _ -> []

evalByName :: MonadTrace Identity m => Int -> Expr -> [m ()]
evalByName n = getPrefixTraces n . Template.evalByName

evalByNeed :: MonadTrace Identity m => Int -> Expr -> [m ()]
evalByNeed n = getPrefixTraces n . Template.evalByNeed

evalByValue :: MonadTrace Identity m => Int -> Expr -> [m ()]
evalByValue n = getPrefixTraces n . Template.evalByValue

evalClairvoyant :: MonadTrace Identity m => Int -> Expr -> [m ()]
evalClairvoyant n = getPrefixTraces n . Template.evalClairvoyant

---------------------
-- LogEvents: Collecting semantics that collects transition types
--
newtype LogEvents a = LogEvents { unLogEvents :: Writer String a }
  deriving (Functor,Applicative,Monad,MonadFix)

log :: String -> LogEvents ()
log = LogEvents . tell

instance MonadTrace Identity LogEvents where
  stuck = log "🗲" >> return undefined
  lookup x (Identity m) = log "L" >> m
  app1 m = log "a" >> m
  app2 m = log "A" >> m
  bind m = log "B" >> m
  case1 m = log "c" >> m
  case2 m = log "C" >> m
  update m = log "U" >> m
  let_ m = log "l" >> m

evalLog :: (Int -> Expr -> [LogEvents ()]) -> Int -> Expr -> String
evalLog ev n = execWriter . unLogEvents . last . ev n
