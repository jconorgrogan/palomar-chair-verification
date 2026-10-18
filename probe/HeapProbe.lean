import Lean.Shell

-- Inspect only the compiled max_memory override. Do not change any option or limit.
def main : IO Unit := do
  let compiledDefault := Lean.Internal.getDefaultMaxMemory ()
  let overrides := Lean.Internal.getOptionOverrides ()
  let overrideText := match overrides.find? `max_memory with
    | none => "absent"
    | some (.ofNat value) => s!"nat:{value}"
    | some _ => "other"
  IO.println s!"LEAN_HEAP_PROBE_V1 default_mib={compiledDefault} override={overrideText}"
