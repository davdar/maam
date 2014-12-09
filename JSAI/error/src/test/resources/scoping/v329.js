
var num = 0;
outermost:
for(var i = 0; i < 10; i++){
   for(var j = 0; j < 10 ; j++){
      if(i == 5 && j == 5){
         break outermost;
      }
    num++;
   }
}

print(num);