/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import Bisection
public meta import Bisection
@[expose] public section
namespace SparseCompletion
namespace RationalBisection
#guard run (fun ρ : ℚ => 1 ≤ ρ) 3 0 2 = (3/4,1)
#guard search (fun ρ : ℚ => 0 ≤ ρ) 3 0 2 = (0,0)
#guard search (fun ρ : ℚ => 1 ≤ ρ) 3 0 2 = (3/4,1)
end RationalBisection
end SparseCompletion
