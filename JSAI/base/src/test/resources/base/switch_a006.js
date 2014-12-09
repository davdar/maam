var i = 5;

s = "";
while (true) {
  switch(i) {
    case 5:{ 
       s = s + "case5;"; // s must be hoisted
       do {
           s = s + "do-while;";
       } while(false);
       break;
    }
    case 1: s = s + "case1;";
  }
  s = s + "break";
  break;
}
print(s);
