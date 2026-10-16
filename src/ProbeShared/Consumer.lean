module
public import ProbeShared.Middle
@[expose] public section
namespace ProbeShared
def answer : Nat := seed + 2
theorem answer_eq : answer = 42 := rfl
end ProbeShared
