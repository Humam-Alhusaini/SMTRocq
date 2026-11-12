(**************************************************************************)
(*     SMTCoq -- distributed under the terms of the CeCILL-C licence       *)
(**************************************************************************)
From Stdlib Require Import String List Bool ZArith QArith Zpow_alt.
From SMTCoq.checker.eunoia Require Import EoSyntax EoArithmetic.
Import ListNotations.
Local Open Scope string_scope.
Module EoArithmeticTests.
Import EoArithmetic.
Definition call (op : string) (args : list string) := eval op (map Symbol args).
Example add_big : call "eo::add" ["99999999999999999999999999999999999999"; "1"] = Some (Symbol "100000000000000000000000000000000000000").
Proof. vm_compute. reflexivity. Qed.

Example mul_big : call "eo::mul" ["-99999999999999999999"; "99999999999999999999"] = Some (Symbol "-9999999999999999999800000000000000000001").
Proof. vm_compute. reflexivity. Qed.

Example add_nary : call "eo::add" ["1"; "-2"; "3"; "-4"] = Some (Symbol "-2").
Proof. vm_compute. reflexivity. Qed.

Example mul_nary : call "eo::mul" ["-3"; "-2"; "7"] = Some (Symbol "42").
Proof. vm_compute. reflexivity. Qed.

Example neg_big : call "eo::neg" ["-999999999999999999999999999999999"] = Some (Symbol "999999999999999999999999999999999").
Proof. vm_compute. reflexivity. Qed.

Example negative_zero : call "eo::neg" ["-0"] = Some (Symbol "0").
Proof. vm_compute. reflexivity. Qed.

Example leading_zero : call "eo::add" ["000012"; "-000002"] = Some (Symbol "10").
Proof. vm_compute. reflexivity. Qed.

Example q_add : call "eo::add" ["2/4"; "-1/6"] = Some (Symbol "1/3").
Proof. vm_compute. reflexivity. Qed.

Example q_cancel : call "eo::add" ["-2/7"; "2/7"] = Some (Symbol "0/1").
Proof. vm_compute. reflexivity. Qed.

Example q_integral : call "eo::mul" ["3/4"; "8/3"] = Some (Symbol "2/1").
Proof. vm_compute. reflexivity. Qed.

Example q_neg : call "eo::neg" ["-12/18"] = Some (Symbol "2/3").
Proof. vm_compute. reflexivity. Qed.

Example qdiv_int : call "eo::qdiv" ["-6"; "-8"] = Some (Symbol "3/4").
Proof. vm_compute. reflexivity. Qed.

Example qdiv_rat : call "eo::qdiv" ["2/3"; "-4/9"] = Some (Symbol "-3/2").
Proof. vm_compute. reflexivity. Qed.

Example qdiv_decimal : call "eo::qdiv" ["1.25"; "-0.50"] = Some (Symbol "-5/2").
Proof. vm_compute. reflexivity. Qed.

Example floor_neg : call "eo::to_z" ["-7/3"] = Some (Symbol "-3").
Proof. vm_compute. reflexivity. Qed.

Example floor_pos : call "eo::to_z" ["7/3"] = Some (Symbol "2").
Proof. vm_compute. reflexivity. Qed.

Example floor_integral : call "eo::to_z" ["-6/3"] = Some (Symbol "-2").
Proof. vm_compute. reflexivity. Qed.

Example floor_small_neg : call "eo::to_z" ["-1/99999999999999999999999"] = Some (Symbol "-1").
Proof. vm_compute. reflexivity. Qed.

Example floor_integer : call "eo::to_z" ["-123"] = Some (Symbol "-123").
Proof. vm_compute. reflexivity. Qed.

Example to_q_integer : call "eo::to_q" ["-123"] = Some (Symbol "-123/1").
Proof. vm_compute. reflexivity. Qed.

Example to_q_reduce : call "eo::to_q" ["-120/180"] = Some (Symbol "-2/3").
Proof. vm_compute. reflexivity. Qed.

Example to_q_decimal : call "eo::to_q" ["-001.2500"] = Some (Symbol "-5/4").
Proof. vm_compute. reflexivity. Qed.

Example to_q_minus_dot : call "eo::to_q" ["-.5"] = Some (Symbol "-1/2").
Proof. vm_compute. reflexivity. Qed.

Example decimal_add : call "eo::add" ["1.20"; "-0.2"] = Some (Symbol "1.0").
Proof. vm_compute. reflexivity. Qed.

Example decimal_mul : call "eo::mul" ["-0.025"; "0.2"] = Some (Symbol "-0.005").
Proof. vm_compute. reflexivity. Qed.

Example decimal_neg_zero : call "eo::neg" ["-0.00"] = Some (Symbol "0.0").
Proof. vm_compute. reflexivity. Qed.

Example decimal_pad : call "eo::neg" ["0.00000001"] = Some (Symbol "-0.00000001").
Proof. vm_compute. reflexivity. Qed.

Example decimal_floor : call "eo::to_z" ["-1.0001"] = Some (Symbol "-2").
Proof. vm_compute. reflexivity. Qed.

Example is_z : call "eo::is_z" ["12"] = Some (Symbol "true").
Proof. vm_compute. reflexivity. Qed.

Example is_z_neg : call "eo::is_z" ["-12"] = Some (Symbol "true").
Proof. vm_compute. reflexivity. Qed.

Example is_z_rat : call "eo::is_z" ["12/1"] = Some (Symbol "false").
Proof. vm_compute. reflexivity. Qed.

Example is_q_integer : call "eo::is_q" ["12"] = Some (Symbol "false").
Proof. vm_compute. reflexivity. Qed.

Example is_q : call "eo::is_q" ["12/1"] = Some (Symbol "true").
Proof. vm_compute. reflexivity. Qed.

Example is_q_decimal : call "eo::is_q" ["12.0"] = Some (Symbol "false").
Proof. vm_compute. reflexivity. Qed.

Example is_q_symbol : call "eo::is_q" ["x"] = Some (Symbol "false").
Proof. vm_compute. reflexivity. Qed.

Example is_neg : call "eo::is_neg" ["-1/2"] = Some (Symbol "true").
Proof. vm_compute. reflexivity. Qed.

Example is_neg_zero : call "eo::is_neg" ["-0/2"] = Some (Symbol "false").
Proof. vm_compute. reflexivity. Qed.

Example is_neg_pos : call "eo::is_neg" ["0.1"] = Some (Symbol "false").
Proof. vm_compute. reflexivity. Qed.

Example gt_integer : call "eo::gt" ["999999999999999999999"; "999999999999999999998"] = Some (Symbol "true").
Proof. vm_compute. reflexivity. Qed.

Example gt_rat : call "eo::gt" ["-1/3"; "-1/2"] = Some (Symbol "true").
Proof. vm_compute. reflexivity. Qed.

Example gt_equal : call "eo::gt" ["2/6"; "1/3"] = Some (Symbol "false").
Proof. vm_compute. reflexivity. Qed.

Example gt_decimal : call "eo::gt" ["1.00"; "0.99999999999999999999"] = Some (Symbol "true").
Proof. vm_compute. reflexivity. Qed.

Example power_zero : call "eo::pow" ["0"; "0"] = Some (Symbol "1").
Proof. vm_compute. reflexivity. Qed.

Example power_negative_base : call "eo::pow" ["-2"; "101"] = Some (Symbol "-2535301200456458802993406410752").
Proof. vm_compute. reflexivity. Qed.

Example power_rational : call "eo::pow" ["-2/3"; "3"] = Some (Symbol "-8/27").
Proof. vm_compute. reflexivity. Qed.

Example power_decimal : call "eo::pow" ["-0.50"; "3"] = Some (Symbol "-0.125").
Proof. vm_compute. reflexivity. Qed.

Example power_decimal_zero : call "eo::pow" ["2.00"; "0"] = Some (Symbol "1.0").
Proof. vm_compute. reflexivity. Qed.

Example log_base2 : call "eo::log" ["2"; "1024"] = Some (Symbol "10").
Proof. vm_compute. reflexivity. Qed.

Example log_below_power : call "eo::log" ["2"; "1023"] = Some (Symbol "9").
Proof. vm_compute. reflexivity. Qed.

Example log_rational : call "eo::log" ["2"; "2049/2"] = Some (Symbol "10").
Proof. vm_compute. reflexivity. Qed.

Example log_decimal : call "eo::log" ["3"; "80.999"] = Some (Symbol "3").
Proof. vm_compute. reflexivity. Qed.

Example log_bad_base : call "eo::log" ["1"; "100"] = Some (Symbol "0").
Proof. vm_compute. reflexivity. Qed.

Example log_neg_base : call "eo::log" ["-2"; "100"] = Some (Symbol "0").
Proof. vm_compute. reflexivity. Qed.

Example log_neg_value : call "eo::log" ["2"; "-4/3"] = Some (Symbol "0").
Proof. vm_compute. reflexivity. Qed.

Example log_small_value : call "eo::log" ["2"; "1/2"] = Some (Symbol "0").
Proof. vm_compute. reflexivity. Qed.

Example log_zero : call "eo::log" ["2"; "0"] = Some (Symbol "0").
Proof. vm_compute. reflexivity. Qed.

Example div_p7_p3 : call "eo::zdiv" ["7"; "3"] = Some (Symbol "2").
Proof. vm_compute. reflexivity. Qed.

Example mod_p7_p3 : call "eo::zmod" ["7"; "3"] = Some (Symbol "1").
Proof. vm_compute. reflexivity. Qed.

Example div_p7_n3 : call "eo::zdiv" ["7"; "-3"] = Some (Symbol "-2").
Proof. vm_compute. reflexivity. Qed.

Example mod_p7_n3 : call "eo::zmod" ["7"; "-3"] = Some (Symbol "1").
Proof. vm_compute. reflexivity. Qed.

Example div_n7_p3 : call "eo::zdiv" ["-7"; "3"] = Some (Symbol "-3").
Proof. vm_compute. reflexivity. Qed.

Example mod_n7_p3 : call "eo::zmod" ["-7"; "3"] = Some (Symbol "2").
Proof. vm_compute. reflexivity. Qed.

Example div_n7_n3 : call "eo::zdiv" ["-7"; "-3"] = Some (Symbol "3").
Proof. vm_compute. reflexivity. Qed.

Example mod_n7_n3 : call "eo::zmod" ["-7"; "-3"] = Some (Symbol "2").
Proof. vm_compute. reflexivity. Qed.

Example div_p6_p3 : call "eo::zdiv" ["6"; "3"] = Some (Symbol "2").
Proof. vm_compute. reflexivity. Qed.

Example mod_p6_p3 : call "eo::zmod" ["6"; "3"] = Some (Symbol "0").
Proof. vm_compute. reflexivity. Qed.

Example div_p6_n3 : call "eo::zdiv" ["6"; "-3"] = Some (Symbol "-2").
Proof. vm_compute. reflexivity. Qed.

Example mod_p6_n3 : call "eo::zmod" ["6"; "-3"] = Some (Symbol "0").
Proof. vm_compute. reflexivity. Qed.

Example div_n6_p3 : call "eo::zdiv" ["-6"; "3"] = Some (Symbol "-2").
Proof. vm_compute. reflexivity. Qed.

Example mod_n6_p3 : call "eo::zmod" ["-6"; "3"] = Some (Symbol "0").
Proof. vm_compute. reflexivity. Qed.

Example div_n6_n3 : call "eo::zdiv" ["-6"; "-3"] = Some (Symbol "2").
Proof. vm_compute. reflexivity. Qed.

Example mod_n6_n3 : call "eo::zmod" ["-6"; "-3"] = Some (Symbol "0").
Proof. vm_compute. reflexivity. Qed.

Example div_p1_p3 : call "eo::zdiv" ["1"; "3"] = Some (Symbol "0").
Proof. vm_compute. reflexivity. Qed.

Example mod_p1_p3 : call "eo::zmod" ["1"; "3"] = Some (Symbol "1").
Proof. vm_compute. reflexivity. Qed.

Example div_p1_n3 : call "eo::zdiv" ["1"; "-3"] = Some (Symbol "0").
Proof. vm_compute. reflexivity. Qed.

Example mod_p1_n3 : call "eo::zmod" ["1"; "-3"] = Some (Symbol "1").
Proof. vm_compute. reflexivity. Qed.

Example div_n1_p3 : call "eo::zdiv" ["-1"; "3"] = Some (Symbol "-1").
Proof. vm_compute. reflexivity. Qed.

Example mod_n1_p3 : call "eo::zmod" ["-1"; "3"] = Some (Symbol "2").
Proof. vm_compute. reflexivity. Qed.

Example div_n1_n3 : call "eo::zdiv" ["-1"; "-3"] = Some (Symbol "1").
Proof. vm_compute. reflexivity. Qed.

Example mod_n1_n3 : call "eo::zmod" ["-1"; "-3"] = Some (Symbol "2").
Proof. vm_compute. reflexivity. Qed.

Example div_p0_p3 : call "eo::zdiv" ["0"; "3"] = Some (Symbol "0").
Proof. vm_compute. reflexivity. Qed.

Example mod_p0_p3 : call "eo::zmod" ["0"; "3"] = Some (Symbol "0").
Proof. vm_compute. reflexivity. Qed.

Example div_p0_n3 : call "eo::zdiv" ["0"; "-3"] = Some (Symbol "0").
Proof. vm_compute. reflexivity. Qed.

Example mod_p0_n3 : call "eo::zmod" ["0"; "-3"] = Some (Symbol "0").
Proof. vm_compute. reflexivity. Qed.

Example add_empty : call "eo::add" [] = None.
Proof. vm_compute. reflexivity. Qed.

Example add_unary : call "eo::add" ["1"] = None.
Proof. vm_compute. reflexivity. Qed.

Example mul_empty : call "eo::mul" [] = None.
Proof. vm_compute. reflexivity. Qed.

Example mul_unary : call "eo::mul" ["2"] = None.
Proof. vm_compute. reflexivity. Qed.

Example neg_arity : call "eo::neg" ["1"; "2"] = None.
Proof. vm_compute. reflexivity. Qed.

Example div_arity : call "eo::zdiv" ["2"] = None.
Proof. vm_compute. reflexivity. Qed.

Example mixed_add : call "eo::add" ["1"; "2/1"] = None.
Proof. vm_compute. reflexivity. Qed.

Example mixed_mul : call "eo::mul" ["1/1"; "1.0"] = None.
Proof. vm_compute. reflexivity. Qed.

Example mixed_gt : call "eo::gt" ["1"; "1/1"] = None.
Proof. vm_compute. reflexivity. Qed.

Example mixed_qdiv : call "eo::qdiv" ["1"; "1/2"] = None.
Proof. vm_compute. reflexivity. Qed.

Example decimal_zdiv : call "eo::zdiv" ["1.0"; "2.0"] = None.
Proof. vm_compute. reflexivity. Qed.

Example rational_zmod : call "eo::zmod" ["1/1"; "2/1"] = None.
Proof. vm_compute. reflexivity. Qed.

Example div_zero : call "eo::zdiv" ["1"; "0"] = None.
Proof. vm_compute. reflexivity. Qed.

Example mod_zero : call "eo::zmod" ["1"; "-0"] = None.
Proof. vm_compute. reflexivity. Qed.

Example qdiv_zero_int : call "eo::qdiv" ["1"; "0"] = None.
Proof. vm_compute. reflexivity. Qed.

Example qdiv_zero_rat : call "eo::qdiv" ["1/1"; "-0/7"] = None.
Proof. vm_compute. reflexivity. Qed.

Example qdiv_zero_dec : call "eo::qdiv" ["1.0"; "0.00"] = None.
Proof. vm_compute. reflexivity. Qed.

Example pow_neg : call "eo::pow" ["2"; "-1"] = None.
Proof. vm_compute. reflexivity. Qed.

Example pow_over_uint32 : call "eo::pow" ["2"; "4294967296"] = None.
Proof. vm_compute. reflexivity. Qed.

Example pow_rat_exp : call "eo::pow" ["2"; "3/1"] = None.
Proof. vm_compute. reflexivity. Qed.

Example log_rat_base : call "eo::log" ["2/1"; "4"] = None.
Proof. vm_compute. reflexivity. Qed.

Example unknown : call "eo::div" ["1"; "2"] = None.
Proof. vm_compute. reflexivity. Qed.

Example malformed_empty : call "eo::to_q" [""] = None.
Proof. vm_compute. reflexivity. Qed.

Example malformed_minus : call "eo::to_z" ["-"] = None.
Proof. vm_compute. reflexivity. Qed.

Example malformed_plus : call "eo::add" ["+1"; "2"] = None.
Proof. vm_compute. reflexivity. Qed.

Example malformed_space : call "eo::neg" [" 1"] = None.
Proof. vm_compute. reflexivity. Qed.

Example malformed_trailer : call "eo::neg" ["1x"] = None.
Proof. vm_compute. reflexivity. Qed.

Example malformed_eof : call "eo::neg" ["1 2"] = None.
Proof. vm_compute. reflexivity. Qed.

Example malformed_rational : call "eo::to_q" ["1/2/3"] = None.
Proof. vm_compute. reflexivity. Qed.

Example malformed_den_sign : call "eo::to_q" ["1/-2"] = None.
Proof. vm_compute. reflexivity. Qed.

Example malformed_den_zero : call "eo::to_q" ["1/000"] = None.
Proof. vm_compute. reflexivity. Qed.

Example malformed_num : call "eo::to_q" ["/2"] = None.
Proof. vm_compute. reflexivity. Qed.

Example malformed_den : call "eo::to_q" ["1/"] = None.
Proof. vm_compute. reflexivity. Qed.

Example malformed_decimal : call "eo::to_q" ["1."] = None.
Proof. vm_compute. reflexivity. Qed.

Example malformed_double_dot : call "eo::to_q" ["1.2.3"] = None.
Proof. vm_compute. reflexivity. Qed.

Example malformed_exponent : call "eo::to_q" ["1e3"] = None.
Proof. vm_compute. reflexivity. Qed.

Example malformed_predicate : call "eo::is_z" ["1/0"] = None.
Proof. vm_compute. reflexivity. Qed.

Example malformed_predicate_tail : call "eo::is_q" ["1/2x"] = None.
Proof. vm_compute. reflexivity. Qed.

Example structured_operand_fails :
  eval "eo::neg" [Apply (Symbol "- a") (Symbol "1")] = None.
Proof. reflexivity. Qed.
Example structured_kind_is_false :
  eval "eo::is_z" [Apply (Symbol "f") (Symbol "1")] = Some (Symbol "false").
Proof. reflexivity. Qed.
Example cmp_deferred : supports "eo::cmp" = false.
Proof. reflexivity. Qed.
Example recognized_failure : dispatch "eo::zdiv" [Symbol "1"; Symbol "0"] = Failed.
Proof. vm_compute. reflexivity. Qed.
Example unsupported_is_distinct : dispatch "eo::cmp" [Symbol "1"; Symbol "2"] = Unsupported.
Proof. vm_compute. reflexivity. Qed.
Example rational_normal_form : normalize (Symbol "-00120/00180") = Some (Symbol "-2/3").
Proof. vm_compute. reflexivity. Qed.

Example decimal_normal_form : normalize (Symbol "-001.2500") = Some (Symbol "-1.25").
Proof. vm_compute. reflexivity. Qed.
Example decimal_kind_preserved : normalize (Symbol "001.000") = Some (Symbol "1.0").
Proof. vm_compute. reflexivity. Qed.

Example power_uint32_max : call "eo::pow" ["1"; "4294967295"] = Some (Symbol "1").
Proof. vm_compute. reflexivity. Qed.
Example rational_power_uint32_max : call "eo::pow" ["-1/1"; "4294967295"] = Some (Symbol "-1/1").
Proof. vm_compute. reflexivity. Qed.

Example decimal_power_uint32_max : call "eo::pow" ["1.0"; "4294967295"] = Some (Symbol "1.0").
Proof. vm_compute. reflexivity. Qed.

Print Assumptions Zpower_equiv.
Print Assumptions unsupported_dispatch.
Print Assumptions failed_dispatch.
Print Assumptions euclidean_equation.
Print Assumptions euclidean_remainder_bounds.
Print Assumptions zero_division_fails.
End EoArithmeticTests.
