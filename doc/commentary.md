# What happens when we remove A1?

With A1 removed, A2/A6/A8 now say "for any tritone t that may or may not exist, ...". To instantiate those in the ZMod 12 model you have to actually find which element is the tritone. zmod12_tritone_is_six is that finding — it's a computation in ZMod 12 arithmetic that says 6 is the unique self-inverse non-zero element.

The deeper point: zmod12_tritone_is_six is provable from ZMod 12 arithmetic alone, without any of the musical axioms. It is, in effect, a local substitute for A1 inside the consistency proof. Its presence signals that zmod12Model is not just showing A2–A8 are satisfiable — it is specifically showing they are satisfiable in a model that also satisfies A1. The lemma smuggles A1's content back in at the model level.

The zmod3Model has no such lemma, and that is the honest witness: A2–A8 hold there because no tritone exists, so the conditional axioms are vacuously true. The constraint zmod3Model actually demonstrates is that A2–A8 are consistent with m = 3, a value that A1 would have ruled out (since 3 is odd, so 2t = 0 would force t = 0).