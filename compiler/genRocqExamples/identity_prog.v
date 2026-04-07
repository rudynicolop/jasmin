Require Export Jasmin.expr.
Section prog.
Definition identity := 
{|
f_info := FunInfo.witness;
f_contract := None;
f_typin := [];
f_params := [];
f_body := [];
f_typout := [];
f_res := [];
f_extra := tt|}
.
End prog.
