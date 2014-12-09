var fs = require('fs');
var UglifyJS = require('uglify-js');

// takes an object where the keys are variable names
function printsFromDistinctVariables(vars) {
    var keys = Object.keys(vars).sort();
    return keys.map(function (varName) {
	return new UglifyJS.AST_SimpleStatement({
	    body: new UglifyJS.AST_Call({
		expression: new UglifyJS.AST_SymbolRef({name: 'print'}),
		args: [new UglifyJS.AST_SymbolRef({name: varName})]
	    })
	});
    });
}

function addPrintsForVariables(node, vars, where) {
    var calls = printsFromDistinctVariables(vars);
    if (calls.length > 0) {
	// unshift breaks horribly...no idea why
	if (where === 'start') {
	    node.body.forEach(function (f) {calls.push(f);});
	    node.body = calls;
	} else if (where === 'end') {
	    calls.forEach(function (c) {node.body.push(c);});
	} else {
	    throw new Error("where must be either 'start' or 'end'");
	}
    }
}

var transformer = new UglifyJS.TreeTransformer(null, function (node) {
    var distinctVariables = {}; // not sure if this is redundant
    function addNodeScope(scope) {
	if (scope !== null) {
	    addVariables(scope.variables);
	    addNodeScope(scope.parent_scope);
	}
    }

    function addVariables(variables) {
	variables.each(function (value, key) {
	    distinctVariables[value.name] = 1;
	});
    }
    function addPrints(where) {
	addPrintsForVariables(node, distinctVariables, where);
    }
    if (node instanceof UglifyJS.AST_Lambda) {
	// add everything that's in the parent scope
	addNodeScope(node.parent_scope);

	// add everything from the function arguments
	node.argnames.forEach(function (funarg) {
	    distinctVariables[funarg.name] = 1;
	});

	addPrints('start');

	return node;
    } else if (node instanceof UglifyJS.AST_Toplevel) {
	// add everything from our scope
	addNodeScope(node);
	addPrints('end');
	return node;
    }
});

if (process.argv.length != 4) {
    console.log("Needs an input and an output JS file.");
} else {
    var code = fs.readFileSync(process.argv[2], 'utf-8');
    var ast = UglifyJS.parse(code);
    ast.figure_out_scope();

    var ast2 = ast.transform(transformer);
    fs.writeFileSync(process.argv[3],
		     ast2.print_to_string({ beautify: true }));
}

