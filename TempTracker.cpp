#include <iostream>
#include <vector>
using namespace std;

class TempTracker{
  int mean,min,max,numofTemps;
  int fahrs[111];
  float mode,actual_mean;

  public:
  TempTracker(){
    min=999;
    max=-999;
    numofTemps=0;
    memset(fahrs,0,sizeof(fahrs));
  }
  void insert(int temp){
    if(min>temp)
      min=temp;
    if(max<temp)
      max=temp;
    actual_mean = actual_mean*numofTemps;
    actual_mean += temp;
    actual_mean /= (numofTemps+1);
    mean = int(actual_mean);
    numofTemps++;
    fahrs[temp]++;
  }
  int get_min(){
    return min;
  }
  int get_max(){
    return max;
  }
  int get_mean(){
    return mean;
  }
  float get_mode(){
    int most=-1;
    int index=-1;
    for(int i = 0 ; i<=110; i++){
      if(fahrs[i]>most){
        most=fahrs[i];
        index=i;
      }
    }
    return index;
  }
};


int main(){
  TempTracker TT;
  TT.insert(20);
  TT.insert(15);
  TT.insert(32);
  TT.insert(10);
  TT.insert(32);
  TT.insert(10);
  TT.insert(10);
  cout<<"The max is "<<TT.get_max()<<endl;
  cout<<"The min is "<<TT.get_min()<<endl;
  cout<<"The mean is "<<TT.get_mean()<<endl;
  cout<<"The mode is "<<TT.get_mode()<<endl;
  return 0;

}
