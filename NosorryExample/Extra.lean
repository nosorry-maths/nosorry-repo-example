module

public import Mathlib

/-! A helper module (it exists to make this example a multi-module proof). -/
namespace NosorryExample

theorem two_le_two_add (n : ℕ) : 2 ≤ 2 + n := Nat.le_add_right 2 n

end NosorryExample
