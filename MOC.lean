namespace hidden

inductive exp : Type
| num : ℕ → exp
| add : exp → exp → exp

namespace exp

infixl `+` := add

def eval : exp → ℕ
| (num x) := x
| (exp1 + exp2) := eval exp1 + eval exp2

theorem normal_forms (e : exp) : (∃ x : ℕ, eval e = x) :=
begin

  induction e,

    -- Base case
    case num a 
    { exact ⟨eval (num a), by refl⟩ },

    -- Recursive case
    case add exp1 exp2
    { have inductive_step : ∃ x : ℕ, eval exp1 + eval exp2 = x,
      from 
        match ih_1, ih_2 with
          ⟨y, exp1_norm⟩, ⟨z, exp2_norm⟩ := ⟨(y + z), by rw [exp1_norm, exp2_norm]⟩
        end,
      exact ⟨eval (exp1 + exp2), by refl⟩,
    },

end

end exp
end hidden