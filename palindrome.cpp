#include <iostream>
#include <string>
using namespace std;

bool checkBit(int bit){
  int numOfOnes=0;
  for(int i = 0 ; i < 26; i++){
    int newBit = (1<<i);
    if((newBit&bit)>0)
      numOfOnes++;
  }
  if(numOfOnes>1)
    return false;
  return true;
}

bool checkPalin(string s, int bit){
  for(int i = 0 ;i<s.size(); i++){
    int loc = s[i]-'a';
    bit=bit^(1<<loc);
  }
  return checkBit(bit);
}

int main(){
  int bitVec = 0;
  string palin;
  cin>>palin;
  bool flag = checkPalin(palin,bitVec);
  if(flag)
    cout<<"A permutation is a palindrome!"<<endl;
  else
    cout<<"No palindrome can be made!"<<endl;
}
