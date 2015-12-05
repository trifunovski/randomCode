#include <iostream>

using namespace std;

int main(){
  int m,n;

  cin>>n;
  cin>>m;
  int denoms[m];
  int sum[n+1];
  memset(sum, 0, sizeof(sum));

  for(int i=0;i<m;i++)
    cin>>denoms[i];

  sum[0]=1;

  for(int i=0;i<m;i++){
    for(int j=denoms[i]; j<=n; j++){
      sum[j]+=sum[j-denoms[i]];
    }
  }
  cout<<sum[n]<<endl;
  return 0;
}
