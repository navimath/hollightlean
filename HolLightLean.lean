-- Root module of the `HolLightLean` library.
-- Importing `after_real` pulls in the whole dependency chain:
--   conectors -> meta -> up_to_real -> hol_up_real_terms
--                                   -> hol_up_real_opam
--                                   -> real_align -> after_real
import HolLightLean.after_real
