theory FO_Proofs0
  imports T_Specification
begin

(* This definitions are needed both in FO_Proofs and FO_Proofs_Very_Slow, thus we
   unfortunately have a separate theory file just for them.  *)
definition "mk_Hq Hq H0 G pk m = (if m \<in> msg_spaceT G then Hq (encrT G pk m) else (H0 m::key))"
definition "mk_Hq' Hq H0 g pk m = (if m \<in> msg_space () then Hq (encr () pk m g) else (H0 m::key))"

end
