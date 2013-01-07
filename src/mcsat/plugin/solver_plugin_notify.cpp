#include "mcsat/plugin/solver_plugin_notify.h"
#include "mcsat/plugin/solver_plugin.h"

#include <cstdarg>

using namespace CVC4;
using namespace mcsat;

using namespace std;

void NotificationDispatch::addPlugin(SolverPlugin* plugin) {
    const notification_set& s = plugin->getNotificationTypes();
    notification_set::const_iterator it = s.begin();
    for(; it != s.end(); ++ it) {
      NotificationType type = *it;
      if (type >= d_toNotify.size()) {
	d_toNotify.resize(type + 1);	
      }
      d_toNotify[type].push_back(plugin);
    }
}

void NotificationDispatch::notifyAssertion(TNode assertion) {
  for(unsigned i = 0; i < d_toNotify[NOTIFY_ASSERTION].size(); ++ i) {
    d_toNotify[NOTIFY_ASSERTION][i]->notifyAssertion(assertion);
  }  
}

void NotificationDispatch::notifyRestart() {
  for(unsigned i = 0; i < d_toNotify[NOTIFY_RESTART].size(); ++ i) {
    d_toNotify[NOTIFY_RESTART][i]->notifyRestart();
  }  
}

void NotificationDispatch::notifyConflict() {
  for(unsigned i = 0; i < d_toNotify[NOTIFY_CONFLICT].size(); ++ i) {
    d_toNotify[NOTIFY_CONFLICT][i]->notifyConflict();
  }  
}
  
void NotificationDispatch::notifyConflictResolution(CRef clause) {
  for(unsigned i = 0; i < d_toNotify[NOTIFY_CONFLICT_RESOLUTION].size(); ++ i) {
    d_toNotify[NOTIFY_CONFLICT_RESOLUTION][i]->notifyConflictResolution(clause);
  }  
}
  
void NotificationDispatch::notifyBackjump(const std::vector<Variable>& vars) {
  for(unsigned i = 0; i < d_toNotify[NOTIFY_BACKJUMP].size(); ++ i) {
    d_toNotify[NOTIFY_BACKJUMP][i]->notifyBackjump(vars);
  }  
}
