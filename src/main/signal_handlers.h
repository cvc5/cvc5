#ifndef CVC4__MAIN__SIGNAL_HANDLERS_H
#define CVC4__MAIN__SIGNAL_HANDLERS_H

namespace CVC4 {
namespace main {
namespace signal_handlers {

void timeout_handler();

void install();
void cleanup();

}  // namespace signal_handlers
}  // namespace main
}  // namespace CVC4

#endif /* CVC4__MAIN__SIGNAL_HANDLERS_H */
