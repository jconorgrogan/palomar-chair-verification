# Inactive H5 raw-auditor AS24 proposal

Only the exact audit-AuditHigherPhysicalEndpoints command receives a 24 GiB per-process virtual-address-space limit. Every other command keeps 12 GiB AS. The sampled process-tree RSS ceiling remains 8 GiB; Lean -M4096, argv, source, theorem, auditor, import policy, time, log, file and cleanup limits remain unchanged.

The fixed IR matched its authenticated 1,054,344-byte H0 SHA immediately before the last failed raw audit. That audit's maximum sampled individual virtual size equaled its 12 GiB AS ceiling, while sampled RSS was below 8 GiB. This supports testing virtual-address headroom; it does not establish errno, malloc failure, guaranteed VmPeak, or successful future auditing. A 24 GiB virtual allowance is not a 24 GiB resident-memory reservation. Existing sampled RSS enforcement remains unchanged, including its sampling limitations.

The failed run 39150122418/1 at 31143d79da8970f60dec6227cb97fd5470321209 and its previous contract are retained under origin/. No H5 object artifact survived. Only the original 27 H5 modules are recompiled; all seven fixed predecessor producers and their native admission requirements remain unchanged.

Branch verify/higher-h5-as24-20261018; workflow .github/workflows/conditional-geometry.yml. This contract and workflow are inactive pending independent source review and any separately authorized activation. No runtime result, proof acceptance or publication is claimed by these source checks.
