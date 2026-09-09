# open_proof_network_precheck

A scratch repository. It holds nothing but short-lived job branches and two workflows, it has
no authority, and the gate never reads it (D-35). Its contents may be deleted at any time.

This is where `POST /precheck` runs (D-28): the protocol service pushes a `job/<id>` branch
carrying a submitted bundle, dispatches `precheck.yml`, and that workflow runs the same gate
checks the authoritative gate runs — inside the same container image, on a throwaway VM, so a
contributor's Lean executes nowhere that anyone administers (D-4, D-24).

Nothing here is evidentiary. The mathematics lives in
[open_proof_network_graph](https://github.com/thisisanameforsure/open_proof_network_graph);
the tooling lives in
[open_proof_network](https://github.com/thisisanameforsure/open_proof_network), which is where
these workflows are authored and versioned, under `gate/precheck/`.

Job branches are deleted after seven days by `cleanup.yml`.
