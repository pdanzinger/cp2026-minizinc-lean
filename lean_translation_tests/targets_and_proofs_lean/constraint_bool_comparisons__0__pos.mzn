annotation redundant;
annotation nonredundant;


constraint (
    true == true /\
    false == false /\
    true != false /\
    false != true /\

    true >= false /\
    true > false /\
    false <= true /\
    false < true /\

    true <= true /\
    false <= false /\
    true >= true /\
    false >= false
) :: redundant;


solve satisfy;
