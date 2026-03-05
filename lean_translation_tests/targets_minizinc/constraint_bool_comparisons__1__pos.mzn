annotation redundant;
annotation nonredundant;constraint (not ((not(
    true != true \/
    false != false \/
    true == false \/
    false == true \/
    true <= false \/
    true < false \/
    false >= true \/
    false > true
))));



solve satisfy;
