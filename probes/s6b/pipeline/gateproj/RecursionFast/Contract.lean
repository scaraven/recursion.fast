/-! Stand-in for the trusted contract root (Lean core only). -/
namespace RecursionFast
/-- A "verification key" computed by the submission's indexer; the certificate pins its value. -/
structure Sub where
  vk : Nat
end RecursionFast
