#include <iostream>
#include <vector>
#include <unordered_map>

using namespace std;

struct meet{
  int start;
  int end;
  string id;
};

bool byStart(meet a, meet b)
{
  return a.start < b.start;
}

int main(){
  int n,s,e;
  string id;
  vector<meet> meetings, timesTaken;
  vector<string> clashes;
  cin>>n;
  for(int i = 0; i<n; i++)
  {
    cin>>s>>e>>id;
    meet m1;
    m1.start = s;
    m1.end = e;
    m1.id = id;
    meetings.push_back(m1);
  }

  unordered_map<int,int> ht;
  sort(meetings.begin(),meetings.end(),byStart);

  ht[meetings[0].start]=meetings[0].end;
  int curr = 0;
  for(int i = 1; i<n; i++){
    if(meetings[i].start>=meetings[curr].start && meetings[i].start<=ht[meetings[curr].start])
    {
      if(meetings[i].end>ht[meetings[curr].start]){
        ht[meetings[curr].start]=meetings[i].end;
      }
      clashes.push_back(meetings[curr].id);
      clashes.push_back(meetings[i].id);
    }
    else{
      ht[meetings[i].start]=meetings[i].end;
      curr = i;
    }
  }

  for(int i = 0; i<n; i++){
    if(ht[meetings[i].start]!=NULL){
      meet m;
      m.start = meetings[i].start;
      m.end = ht[meetings[i].start];
      timesTaken.push_back(m);
    }
  }
  cout<<endl;
  for(int i = 0; i<timesTaken.size(); i++)
    cout<<timesTaken[i].start<<","<<timesTaken[i].end<<endl;

  cout<<endl;
  sort(clashes.begin(),clashes.end());

  for(int i = 0; i<clashes.size();i++){
    if(i+1==clashes.size())
      cout<<clashes[i]<<endl;
    else if(clashes[i]!=clashes[i+1])
      cout<<clashes[i]<<endl;
  }
}
