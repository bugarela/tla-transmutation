-------------------------------- MODULE typedefs ------------------------------
(*
## Type aliases

  We introduce the following aliases for the types that are used in this
  specification.

  @typeAlias: CHAIN = Str;
  @typeAlias: ACCOUNT = Str;
  @typeAlias: ADDR = <<CHAIN, ACCOUNT>>;
  @typeAlias: BANK = (ADDR -> Int);

  @typeAlias: DENOM = Str;
  @typeAlias: DADDR = <<CHAIN, ACCOUNT, DENOM>>;
 *)
typedefs_included == TRUE
===============================================================================
