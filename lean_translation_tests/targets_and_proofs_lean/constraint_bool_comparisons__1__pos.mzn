annotation redundant;
annotation nonredundant;

constraint (not(
    true != true \/
    false != false \/
    true == false \/
    false == true \/
    true <= false \/
    true < false \/
    false >= true \/
    false > true
)) :: redundant;


solve satisfy;
