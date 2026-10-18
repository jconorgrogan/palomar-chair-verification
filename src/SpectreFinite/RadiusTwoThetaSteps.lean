module

public import SpectreFinite.RadiusTwoTable1
public import SpectreFinite.RadiusTwoTable3
public import SpectreFinite.RadiusTwoTable5
public import SpectreFinite.RadiusTwoTable6
public import SpectreFinite.RadiusTwoTable13
public import SpectreFinite.RadiusTwoTable15

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def thetaDomains0 : Domains 19 State := domains (2,0)
def thetaDomains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => stateChoices
  | 2 => stateChoices
  | 3 => stateChoices
  | 4 => stateChoices
  | 5 => stateChoices
  | 6 => stateChoices
  | 7 => stateChoices
  | 8 => [(0,5)]
  | 9 => [(2,0)]
  | 10 => stateChoices
  | 11 => stateChoices
  | 12 => [(6,0)]
  | 13 => [(3,1)]
  | 14 => [(0,1)]
  | 15 => stateChoices
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | _ => stateChoices
theorem thetaStep1_checked :
    checkReplacement table13 thetaDomains0 thetaDomains1 = true := by decide
def thetaDomains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => [(0,0),(1,3)]
  | 2 => [(4,2),(7,2)]
  | 3 => stateChoices
  | 4 => [(1,5),(6,5)]
  | 5 => [(0,4),(6,1)]
  | 6 => [(3,4),(4,1)]
  | 7 => stateChoices
  | 8 => [(0,5)]
  | 9 => [(2,0)]
  | 10 => [(2,3),(7,3)]
  | 11 => stateChoices
  | 12 => [(6,0)]
  | 13 => [(3,1)]
  | 14 => [(0,1)]
  | 15 => stateChoices
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | _ => stateChoices
theorem thetaStep2_checked :
    checkReplacement table5 thetaDomains1 thetaDomains2 = true := by decide
def thetaDomains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(3,4),(5,4)]
  | 1 => [(0,0),(1,3)]
  | 2 => [(4,2),(7,2)]
  | 3 => [(4,3)]
  | 4 => [(1,5),(6,5)]
  | 5 => [(0,4),(6,1)]
  | 6 => [(3,4),(4,1)]
  | 7 => [(1,4)]
  | 8 => [(0,5)]
  | 9 => [(2,0)]
  | 10 => [(2,3),(7,3)]
  | 11 => stateChoices
  | 12 => [(6,0)]
  | 13 => [(3,1)]
  | 14 => [(0,1)]
  | 15 => stateChoices
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | _ => stateChoices
theorem thetaStep3_checked :
    checkReplacement table3 thetaDomains2 thetaDomains3 = true := by decide
def thetaDomains4 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(3,4),(5,4)]
  | 1 => [(0,0),(1,3)]
  | 2 => [(4,2),(7,2)]
  | 3 => [(4,3)]
  | 4 => [(1,5),(6,5)]
  | 5 => [(0,4),(6,1)]
  | 6 => [(3,4),(4,1)]
  | 7 => [(1,4)]
  | 8 => [(0,5)]
  | 9 => [(2,0)]
  | 10 => [(2,3),(7,3)]
  | 11 => [(0,2),(4,2),(5,2),(8,2)]
  | 12 => [(6,0)]
  | 13 => [(3,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | _ => [(1,0)]
theorem thetaStep4_checked :
    checkReplacement table15 thetaDomains3 thetaDomains4 = true := by decide
def thetaDomains5 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(4,3)]
  | 4 => [(1,5)]
  | 5 => [(6,1)]
  | 6 => [(3,4),(4,1)]
  | 7 => [(1,4)]
  | 8 => [(0,5)]
  | 9 => [(2,0)]
  | 10 => [(2,3),(7,3)]
  | 11 => [(0,2),(4,2),(5,2),(8,2)]
  | 12 => [(6,0)]
  | 13 => [(3,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | _ => [(1,0)]
theorem thetaStep5_checked :
    checkReplacement table1 thetaDomains4 thetaDomains5 = true := by decide
def thetaDomains6 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(4,3)]
  | 4 => [(1,5)]
  | 5 => [(6,1)]
  | 6 => [(4,1)]
  | 7 => [(1,4)]
  | 8 => [(0,5)]
  | 9 => [(2,0)]
  | 10 => [(7,3)]
  | 11 => [(5,2)]
  | 12 => [(6,0)]
  | 13 => [(3,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | _ => [(1,0)]
theorem thetaStep6_checked :
    checkReplacement table6 thetaDomains5 thetaDomains6 = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
