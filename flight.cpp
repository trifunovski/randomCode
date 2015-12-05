#include <iostream>
#include <vector>
#include <unordered_map>
using namespace std;

bool findMovies(vector<int> movie_lengths, int flight_length){
  unordered_map<int,int> ht;
  for(int i = 0; i<movie_lengths.size(); i++)
    ht[movie_lengths[i]]=true;
  for(int i = 0; i<movie_lengths.size(); i++){
    if(ht[flight_length-movie_lengths[i]])
      return true;
  }
  return false;
}

int main(){
  vector<int> movie_lengths;
  int flight_length,a,n;
  cin>>flight_length;
  cin>>n;
  for(int i = 0; i<n; i++){
    cin>>a;
    movie_lengths.push_back(a);
  }
  if(findMovies(movie_lengths,flight_length))
    cout<<"YES"<<endl;
  else
    cout<<"NO"<<endl;
  return 0;
}
