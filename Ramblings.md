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

First off, `L` not simply a lattice, but rather some Monad `AbsM` such that `L = AbsM (Value AbsM)`,
satisfying both the `MonadAlloc` and `MonadTrace` constraints.
Likewise, `Trace` is really `TraceM (Value TraceM)` with its own `MonadAlloc` and `MonadTrace` in turn.

Translated to explicit Dictionary passing, and naming `trc : MonadTrace AbsM` and `allc : MonadAlloc AbsM`,
we can (re-)construct `α : Trace -> L` by simple means from `trc`, e.g.,

  α(Stuck) = trc.stuck
  α(Ret v) = trc.return (α_V v)
  α(Delay (Look as) t) = trc.look as t
  α(Delay (Bind as) t) = trc.bind as t
  ...

  α_V(Fun f) = Fun (α . f . γ)

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
  The correctnes condition for `alloc` might be something like

