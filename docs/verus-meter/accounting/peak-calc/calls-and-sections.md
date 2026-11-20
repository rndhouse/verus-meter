# Calls and sections

- **Calls.** Combine the callee's declared allowance with the caller storage that stays live across the call. Declared slack counts when composing contracts. Passing an owner to a helper preserves the allocation's identity.
- **Sections.** Take the allowance at section entry. The enclosing scope pays for storage already live and the section's allowance. Growth of an enclosing collection inside the section remains with its owner on exit.
