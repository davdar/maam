print(Number.prototype.constructor.length)

Number.prototype.asdf = true;

for(i in new Object(5)) print(i);
for(i in 5) print(i);

