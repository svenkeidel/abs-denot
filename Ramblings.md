# Rough idea

Given an abstraction α :: Trace -> (L, ⊑)

(we can construct a homomorphic Galois connection (P(Trace), ⊆) <-> (L,⊑))

Usually we construct the collecting semantics C[[e]] such that α(S[[e]]) ⊑ C[[e]].
This is entirely mechanical and may or may not lead to a computable C[[_]].

Usually, α :: Trace -> (L, ⊑) is defined as a productive fold over the trace.
Productivity is essential since the trace might be infinite and otherwise the fold would be undefined.
Often, we notice repeated structure in the trace (invariants) and utilise fixpoint iteration.

In a final encoding of Trace, we don't have α :: Trace -> (L,⊑), but rather
encode this productive fold in the type class instance `MonadTrace (L,⊑)`.
Thus, every instance of MonadTrace induces an abstraction.
There are lossless abstractions, for example `MonadTrace (Trace,⊆)`, where {S[[e]]} = γ(C[[e]]).

Associated to every trace monad is an instance of `MonadAlloc`, defining a fixpoint combinator.

# What do we have to show?

First off, `L` not simply a lattice, but rather some Monad `AbsM` such that `L = AbsM (Value AbsM)` (`AbsM L` is a lattice whenever `L` is one),
satisfying both the `MonadAlloc` and `MonadTrace` constraints.
Likewise, `Trace` is really `TraceM (Value TraceM)` with its own `MonadAlloc` and `MonadTrace` in turn.

The `α : Trace -> L` is a special case of a (single-method) type class instance

instance Repr T L => Repr (TraceM T) (AbsM L) where
  α(Stuck) = AbsM.stuck
  α(Ret v) = AbsM.return (α v)
  α(Delay (Look as) t) = AbsM.look as t
  α(Delay (Bind as) t) = AbsM.bind as t
  ...

instance Abs T L => Abs (Value T) (Value L) where
  α(Fun f) = Fun (α . f . γ)

For this to make sense, AbsM must be endofunctors in the category of lattices.
Furthermore, α is not actually computable unless the trace is finite.
(We want something like α(τ) = ⊔_τ*∈pref(τ) α(τ*).
When γ(l) is a safety property for all l, then α(τ) ⊑ ⊔α(τ*) for all prefixes τ*∈pref(τ).)
Hence this is of no consequence for safety properties, because approximating all finite prefixes is sufficient.

and then the correctness criterion is

  α^..(S[[e]] TraceM) ⊑ S[[e]] AbsM

where
  α^..(S)(r) = ⊔_ρ∈γ^.(r) α({S(ρ)}) = α({S(ρ) | ρ∈γ^.(r)})
  γ^.(r) = [ x↦d | d∈γ(r(x)) ]

Let's derive correctness criterions on MonadTrace and MonadAlloc impls from this.
(We'll probalby have to specify CallBy*??)

Case e=x:
  (stuck case: precisely α(stuck) = trc.stuck))
  α^..(S[[x]])(r) = α({ρ(x) | ρ∈γ^.(r)}) ⊑ r(x) = S[[x]] AbsM
  <=>
  α({d | d∈γ(r(x))}) ⊑ r(x)
  <=>
  α(γ(r(x))) ⊑ r(x) follows by Galois (or simply unfolding γ(d') = ∪{d|α(d)⊑d'})
Case e=e' x:
  (stuck case: ...)
    α^..(S)(r)
  = α({app1 (S[[e']](ρ) >>= \(Fun f) -> f ρ(x)) | ρ∈γ^.(r)})
  Here, we need `α(app1 d) ⊑ trc.app1 (α(d)) (which is just `α(app1) ⊑ trc.app1`, or `α . app1 . γ ⊑ trc.app1`) to have
  ⊑ ⊔{trc.app1 α(S[[e']](ρ) >>= \(Fun f) -> f ρ(x)) | ρ∈γ^.(r)} ⊑ app1 (S[[e']](r) trc.>>= \(Fun f) -> f r(x))
  And now we need `α(d >>= k) ⊑ α(d) trc.>>= α(k)`. Again, this constraint follows structurally (α(>>=) ⊏ trc.>>=). Then we have
  ⊑ ⊔{trc.app1 (α(S[[e']](ρ)) trc.>>= α(\(Fun f) -> f (ρ x))) | ρ∈γ^.(r)}
  Relational abstraction + monotonicity (d1 ⊑ d2, v1 ⊑ v2 ==> d1 >>= v1 ⊑ d2 >>= v2):
  ⊑ ⊔{trc.app1 (α(S[[e']](ρ)) trc.>>= α(\(Fun f) -> f (ρ' x))) | ρ',ρ∈γ^.(r)}
  ⊑ trc.app1 (α({S[[e']](ρ) | ρ∈γ^.(r)}) trc.>>= α({\(Fun f) -> f d | d∈γ(r x)})
  From the IH, we have α({S[[e']](ρ) | ρ∈γ^.(r)}) ⊑ S[[e']](r). Furthermore, we have α(k) = α.k.γ_V, so calculate
  ⊑ trc.app1 (S[[e']](r) trc.>>= ⊔({\(Fun f') -> α(γ(f'(α(d)))) | d∈γ(r x)})
  ⊑ trc.app1 (S[[e']](r) trc.>>= ⊔({\(Fun f') -> f'(α(d)) | d∈γ(r x)})
  ⊑ trc.app1 (S[[e']](r) trc.>>= \(Fun f') -> f' (r x))
  = S[[e' x]](r)
Case e=λx.e':
    α^..(S)(r)
  = α({return (Fun (\d -> app2 S[[e']](ρ[x↦d]))) | ρ∈γ^.(r)})
  = ⊔{α(return (Fun (\d -> app2 S[[e']](ρ[x↦d])))) | ρ∈γ^.(r)}
  Need α(return) = α . return . γ ⊑ trc.return
  ⊑ ⊔{trc.return α(Fun (\d -> app2 S[[e']](ρ[x↦d]))) | ρ∈γ^.(r)}
  Monotonicity of trc.return
  ⊑ trc.return ⊔{α(Fun (\d -> app2 S[[e']](ρ[x↦d]))) | ρ∈γ^.(r)}
  ⊑ trc.return ⊔{Fun (\d' -> α({ app2 S[[e']](ρ[x↦d]) | d∈γ(d')})) | ρ∈γ^.(r)}
  α(app2) ⊑ trc.app2
  ⊑ trc.return ⊔{Fun (\d' -> trc.app2 α({S[[e']](ρ[x↦d]) | d∈γ(d')})) | ρ∈γ^.(r)}
  Relational abstraction:
  ⊑ trc.return ⊔{Fun (\d' -> trc.app2 α({S[[e']](ρ) | ρ∈γ^.(r[x↦d'])})) | ρ∈γ^.(r)}
  IH: α({ S[[e']](ρ) | ρ∈γ^.(r[x↦d'])}) ⊑ S[[e']](r[x↦d'])
  ⊑ trc.return ⊔{Fun (\d' -> trc.app2 S[[e']](r[x↦d'])) | ρ∈γ^.(r)}
  Singleton set
  = trc.return (Fun (\d' -> trc.app2 S[[e']](r[x↦d'])))
  = S[[λx.e']](r)
Case e=let x = e1 in e2:
  α(ext x) ⊑ trc.ext x is derivative. (e.g., `α(ext x env d) ⊑ trc.ext x α^.(env) α(d)`)
  Also need α(bind) ⊑ trc.bind.
  Then the IH `α({ S[[e2]](ρ[x↦d]) | ρ∈γ^.(r),d∈γ(d') }) ⊑ S[[e2]](r[x↦d'])`
  implies that `α({ S[[e2]](ρ[x↦d]) | ρ∈γ^.(r) } ⊑ S[[e2]](r[x↦d'])` whenever $α(d) ⊑ d'$ (because then d ∈ γ(d')).
  So we get α(d)⊑d' on the result returned from `alloc`.
  The correctness condition for `alloc x f` is probably something like `α(alloc x f) ⊑ trc.alloc x α(f)` (this is not surprising, but still a profound requirement!),
  where `α(f) = α.f.γ`.
  OBSERVATION: alloc is in fact the *only* method that depends on evaluation order (in a meaningful way).
               This is where we must be smart!

In total, we need:
  * Abstraction lemmas for all type class methods of the form `α(m) ⊑ trc.m`
    (for `return`, `(>>=)`, `app1`, `app2`, ..., `alloc`)
  * Monotonicity for all type class methods

Simple enough. Except for MonadAlloc, but that's the point!
Need to relate MonadAlloc Name with MonadAlloc UTrace

Show stuff for Name, separately show α(Need) ⊑ α(Name) (boring!...? probably can have something like α(ρ) ⊑ α(μ.ρ))


# PRoving alloc correct

instance MonadTrace m => MonadAlloc (ByNeed m) where
  alloc f = do
    a <- ByNeed $ maybe 0 (\(k,_) -> k+1) . L.lookupMax <$> get
    let d = fetch a
    ByNeed $ modify (L.insert a (memo a (f d)))
    return d

vs.

instance MonadAlloc UTrace where
  alloc f = do
    let us = fixIter (\us -> evalDeep (f (UT us Nop)))
    pure (UT us Nop)

(.<=.) :: Us -> Us -> Bool
us1 .<=. us2 = (us1 .⊔. us2) == us2

fixIter :: (Us -> Us) -> Us
fixIter f = go (f S.empty)
  where
  go us = let us' = f us in if us' .<=. us then us' else go us'

evalUTrace :: Expr -> UTrace (Value UTrace)
evalUTrace e = eval e S.empty

nopD :: D UTrace
nopD = UT S.empty Nop

evalDeep :: D UTrace -> Us
evalDeep (UT us v) = go us v
  where
    go us Bot = us
    go us Nop = us
    go us (Ret (Fun f)) = case f nopD of
      UT us2 v -> go (us .+. us2) v

manyfy :: Us -> Us
manyfy = S.map (const W)

nopVal :: Value UTrace
nopVal = Fun (\d -> UT (manyfy (evalDeep d)) Nop)

