var rec = {};
delete(rec.prototype);
var i = 0;
for (j in rec) {
  print(j);
  i += 1;
}
print(i);

