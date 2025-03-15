<start>	::= <type_expression>  
<type_expression> ::= <base_type> | <type_variable> |  "("<type_expression> " " <type_constructor>")" | "(" <type_expression> " " <function_type> " " <type_expression> ")"
<base_type> ::= "bool" | "int" | "nat"
<type_constructor> ::= "list" | "set"
<function_type> ::= "=>" 
<type_variable> ::= <ascii_lowercase_letter> 
