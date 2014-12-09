call = function() {print("call"); return apply() };
apply = function() {print("apply"); return 5};

var res = call() + apply();
print(res);


