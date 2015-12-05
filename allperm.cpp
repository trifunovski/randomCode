#include <iostream>
#include <string>
#include <vector>
using namespace std;

void allPerm(string s, string prefix){
  if(s.size()==0)
    cout<<prefix<<endl;
  else{
    for(int i = 0; i < s.size(); i++)
      allPerm(s.substr(0,i)+s.substr(i+1,s.size()),prefix+s[i]);
  }
}

int main(){
  string s;
  cin>>s;
  allPerm(s,"");
  return 0;
}
