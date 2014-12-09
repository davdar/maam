call = function() {print("call"); return 4};
apply = function() {print("apply"); return 5};

var res = call() + apply();
print(res);


